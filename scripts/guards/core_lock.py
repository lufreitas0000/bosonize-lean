#!/usr/bin/env python3
"""Verify complete Core source files, including proof bodies, against reviewed hashes.

There is deliberately no update command. Baseline changes belong to an explicitly
reviewed Core promotion, and a committed baseline can be selected with --baseline-ref.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

LOCK_FILE = "docs/spec/core_locks.json"


def check(root: Path, baseline: dict) -> list[str]:
    if not isinstance(baseline, dict) or any(
        not isinstance(k, str) or not isinstance(v, str)
        or re.fullmatch(r"[0-9a-f]{64}", v) is None
        for k, v in baseline.items()
    ):
        return ["Invalid Core lock manifest; expected source paths and SHA-256 digests."]
    current = {
        p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted((root / "Bosonize/Core").rglob("*.lean")) if p.is_file()
    }
    errors = [f"Frozen Core file missing: {p}" for p in sorted(baseline.keys() - current.keys())]
    errors += [f"Unreviewed Core file: {p}" for p in sorted(current.keys() - baseline.keys())]
    errors += [f"Frozen Core source changed: {p}" for p in sorted(baseline.keys() & current.keys())
               if baseline[p] != current[p]]
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".")
    parser.add_argument("--baseline-ref", help="Read the reviewed Core manifest from this Git ref.")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    try:
        if args.baseline_ref:
            result = subprocess.run(
                ["git", "-C", str(root), "show", f"{args.baseline_ref}:{LOCK_FILE}"],
                capture_output=True, text=True, check=True,
            )
            baseline = json.loads(result.stdout)
            if json.loads((root / LOCK_FILE).read_text()) != baseline:
                print("[core_lock] Working-tree baseline differs from the approved Git baseline.",
                      file=sys.stderr)
                return 1
        else:
            baseline = json.loads((root / LOCK_FILE).read_text())
        errors = check(root, baseline)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"[core_lock] Cannot verify Core freeze: {error}", file=sys.stderr)
        return 1
    if errors:
        for error in errors:
            print(f"[core_lock] {error}", file=sys.stderr)
        return 1
    print(f"[core_lock] Verified {len(baseline)} complete Core source file(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
