#!/usr/bin/env python3
"""Verify a frozen proof target with fresh isolated staging oleans and axiom audits."""
import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import verify_phase_a as phase_a


def declarations(code):
    model = phase_a.lean.parse_lean(code)
    names = list(model.lemmas)
    names.extend(c.label.split(" ", 1)[1] for c in model.commands if c.kind in
                 {"def", "abbrev", "instance", "structure", "inductive", "class"})
    return names


def dependencies(repo, targets):
    """Compile only reachable staging modules, dependencies first."""
    ordered, active, done = [], set(), set()

    def visit(name):
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or path.parts[0] != "BosonizeStubs" or path.suffix != ".lean":
            raise ValueError(f"Expected a staging Lean source: {name}")
        if name in active:
            raise ValueError(f"Staging import cycle: {name}")
        if name in done:
            return
        active.add(name)
        source = repo / name
        if source.is_symlink() or not source.is_file():
            raise ValueError(f"Missing/unsafe staging dependency: {name}")
        clean, _ = phase_a.lean.strip_lean(source.read_text())
        for line in clean.splitlines():
            match = re.fullmatch(r"\s*(?:public\s+)?import\s+(.+?)\s*", line)
            if match:
                for module in match[1].split():
                    if module.startswith("BosonizeStubs."):
                        visit(module.replace(".", "/") + ".lean")
        active.remove(name)
        done.add(name)
        ordered.append(name)

    for target in targets:
        visit(target)
    return ordered


def compile_modules(repo, names, primary):
    env = os.environ.copy()
    original_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=primary, text=True).strip()
    lean_binary = subprocess.check_output(["lake", "env", "which", "lean"], cwd=primary, text=True).strip()
    with tempfile.TemporaryDirectory(prefix="bosonize-phase-b-") as folder:
        overlay = Path(folder)
        env["LEAN_PATH"] = str(overlay) + os.pathsep + original_path
        for name in names:
            code = (repo / name).read_text(encoding="utf-8")
            clean, mask = phase_a.lean.strip_lean(code)
            if any(t.kind == "id" and t.text.split(".")[-1].strip("«»") in
                   {"sorry", "sorryAx", "admit", "native_decide", "axiom"}
                   for t in phase_a.lean.tokenize(clean, mask)):
                raise ValueError(f"Unproved/forbidden staging dependency: {name}")
            audited = declarations(code)
            candidate = overlay / name
            candidate.parent.mkdir(parents=True, exist_ok=True)
            candidate.write_text(code + "\n" + "\n".join(f"#print axioms {n}" for n in audited) + "\n")
            result = subprocess.run([lean_binary, "-R", str(overlay), "-o", str(candidate.with_suffix(".olean")),
                                     "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-DwarningAsError=true",
                                     str(candidate)], cwd=primary, env=env, text=True, capture_output=True)
            output = result.stdout + result.stderr
            print(output, end="", flush=True)
            if result.returncode or "warning:" in output:
                raise ValueError(f"Fresh warning-as-error compile failed: {name}")
            for n in audited:
                found = re.search(r"'" + re.escape(n) + r"' depends on axioms: \[([^\]]*)\]", output)
                if not found and f"'{n}' does not depend on any axioms" not in output:
                    raise ValueError(f"Missing fresh axiom audit: {n}")
                axioms = {x.strip() for x in found[1].split(",") if x.strip()} if found else set()
                if axioms - phase_a.ALLOWED_AXIOMS:
                    raise ValueError(f"Nonstandard axioms for {n}: {sorted(axioms)}")
            print(f"PASS: {name}, {len(audited)} freshly audited declarations", flush=True)


def verify(repo, targets):
    primary = phase_a.compiler_root(repo)
    baseline = subprocess.check_output(["git", "-C", str(primary), "rev-parse", "HEAD"], text=True).strip()
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        if (repo / name).read_bytes() != (primary / name).read_bytes():
            raise ValueError(f"Compiler dependency baseline differs: {name}")
    subprocess.run(["python3", "scripts/guards/stub_lock.py", "--check", "--strict", "--baseline-ref", baseline], cwd=repo, check=True)
    subprocess.run(["python3", "scripts/guards/core_lock.py", "--baseline-ref", baseline], cwd=repo, check=True)
    # Core cache is rebuilt in the primary checkout; candidate staging never writes there.
    subprocess.run(["lake", "build", "Bosonize"], cwd=primary, check=True)
    compile_modules(repo, dependencies(repo, targets), primary)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+")
    args = parser.parse_args()
    try:
        verify(phase_a.REPO, args.targets)
    except (ValueError, OSError, subprocess.CalledProcessError, phase_a.lean.LeanScanError) as exc:
        print(f"Phase B rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
