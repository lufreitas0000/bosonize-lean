#!/usr/bin/env python3
"""Check and elaborate a Phase A Markdown proposal; never integrate or freeze it."""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts/guards"))
import stub_lock as lean

HEADINGS = ("Source map", "Design and scope", "Lean draft", "Companion notebook", "Review obligations")
ALLOWED_AXIOMS = {"Classical.choice", "propext", "Quot.sound"}


def inspect(text):
    for heading in HEADINGS:
        if f"## {heading}\n" not in text:
            raise ValueError(f"Missing section: ## {heading}")
    blocks = re.findall(r"^```lean\n(.*?)^```\s*$", text, flags=re.M | re.S)
    if len(blocks) != 1:
        raise ValueError("Expected exactly one complete lean fence (combined CH15/A06 candidate)")
    code = blocks[0]
    model = lean.parse_lean(code)
    if not model.lemmas or model.notes:
        raise ValueError("Require named theorem/lemma stubs with explicit := headers and no parser warnings")
    clean, mask = lean.strip_lean(code)
    tokens = lean.tokenize(clean, mask)
    forbidden = {"admit", "sorryAx", "native_decide", "axiom", "opaque", "run_cmd", "run_meta",
                 "initialize", "builtin_initialize", "elab", "elab_rules", "macro", "macro_rules"}
    if any(t.kind == "id" and t.text.split(".")[-1].strip("«»") in forbidden for t in tokens):
        raise ValueError("Forbidden axiom, escape hatch or elaborator command")
    if any(t.text == "#" for t in tokens):
        raise ValueError("Do not put # commands in the draft; the verifier generates its own data audit")
    allowed_commands = {"import", "namespace", "section", "end", "universe", "variable", "open",
                        "noncomputable", "def", "abbrev", "instance", "structure", "inductive", "class"}
    data = []
    for command in model.commands:
        if command.kind not in allowed_commands:
            raise ValueError(f"Unsupported draft command: {command.kind}; ask local reviewer")
        body, body_mask = lean.strip_lean(command.text)
        if any(t.kind == "id" and t.text in {"sorry", "admit", "sorryAx"}
               for t in lean.tokenize(body, body_mask)):
            raise ValueError("Definitions/instances must be complete; no data placeholders")
        if command.kind in {"def", "abbrev", "instance", "structure", "inductive", "class"}:
            name = command.label.split(" ", 1)[1]
            if not re.fullmatch(r"[\w'.]+", name):
                raise ValueError("Give every data declaration an explicit ordinary Lean name for auditing")
            data.append(name)
    starts = lean.find_starts(tokens)
    for index, start in enumerate(starts):
        end = starts[index + 1] if index + 1 < len(starts) else len(tokens)
        group = tokens[start:end]
        decl = next((i for i, t in enumerate(group) if t.text in {"lemma", "theorem"}), None)
        if decl is None:
            continue
        header = lean._find_header_end(group, decl + 2)
        if header is None or [t.text for t in group[header:]] != [":=", "by", "sorry"]:
            raise ValueError("Each lemma/theorem must end with exactly := by sorry")
    return code, data, len(model.lemmas)


def compiler_root(repo):
    # The cycle runner builds its own private transaction checkout before CI.
    # An explicit local override avoids using a moved primary checkout/cache.
    override = os.environ.get("WEBLLM_COMPILER_ROOT")
    if override:
        working = Path(override).resolve()
        expected = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
        actual = subprocess.check_output(["git", "-C", str(working), "rev-parse", "HEAD"], text=True).strip()
        if expected != actual:
            raise ValueError("Explicit compiler checkout differs from candidate HEAD")
        return working
    common = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "--git-common-dir"], text=True).strip()
    primary = (repo / common).resolve().parent
    # Phase A proposals import immutable Core only. Reuse the checked primary
    # checkout's existing Lake dependencies; never share a mutable staging build.
    original = subprocess.check_output(["git", "-C", str(primary), "rev-parse", "HEAD"], text=True).strip()
    candidate = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    if original != candidate:
        raise ValueError("Primary checkout moved since packet baseline; regenerate")
    return primary


def verify(path, repo=REPO):
    code, data, theorem_count = inspect(Path(path).read_text(encoding="utf-8"))
    # Restrict dependencies to the completed Core aggregator or Core modules.
    imports = [c.text for c in lean.parse_lean(code).commands if c.kind == "import"]
    if not imports or any(not re.fullmatch(r"import Bosonize(?:\.Core\.[\w]+)?", item) for item in imports):
        raise ValueError("Use separate imports of Bosonize or Bosonize.Core.<module>; no new staging/dependency imports")
    working = compiler_root(repo)
    subprocess.run(["python3", "scripts/guards/core_lock.py"], cwd=working, check=True)
    with tempfile.TemporaryDirectory(prefix="bosonize-phase-a-") as folder:
        candidate = Path(folder) / "Candidate.lean"
        candidate.write_text(code + "\n" + "\n".join(f"#print axioms {name}" for name in data) + "\n", encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                                 str(candidate)], cwd=working, capture_output=True, text=True)
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        if result.returncode:
            raise ValueError("Draft did not elaborate; use the actual compiler output as model feedback")
        output = result.stdout + result.stderr
        for name in data:
            match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", output)
            no_axioms = f"'{name}' does not depend on any axioms" in output
            if not match and not no_axioms:
                raise ValueError(f"Missing fresh data axiom output: {name}")
            axioms = set(x.strip() for x in match[1].split(",") if x.strip()) if match else set()
            if axioms - ALLOWED_AXIOMS:
                raise ValueError(f"Data declaration {name} depends on unapproved axioms: {sorted(axioms)}")
        for line in output.splitlines():
            if "warning:" in line and not re.search(r"warning: declaration uses [`']sorry[`']\s*$", line):
                raise ValueError("Non-placeholder warning must be resolved before Phase A acceptance")
    print(f"Phase A artifact ELABORATED: {len(data)} audited data declarations; {theorem_count} unproved theorem stubs.")
    print("Not proved, not independently reviewed, not staged, and not locked. Local mathematical review is next.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proposal", type=Path)
    args = parser.parse_args()
    try:
        verify(args.proposal)
    except (ValueError, OSError, subprocess.CalledProcessError, lean.LeanScanError) as exc:
        print(f"Phase A rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
