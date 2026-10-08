#!/usr/bin/env python3
"""
stub_lock.py -- statement-freeze guard for Lean staging files (BosonizeStubs).

Purpose
-------
Stop an agent (or a tired human) from "proving" a lemma by quietly changing
its statement, its definitions, or the context it is elaborated in.

What is frozen (v2)
-------------------
For every `*.lean` file under the guarded directories the file is split into
top-level commands (comments and string literals are understood, brackets are
tracked).  Then:

  * `theorem` / `lemma`  -> the HEADER is frozen: modifiers, attributes,
                            `open .. in` prefixes, name, binders, hypotheses,
                            conclusion (everything before the top-level `:=`).
                            The proof body is NOT frozen.
  * EVERYTHING else      -> the whole command is frozen, in order:
                            def / abbrev / instance / structure / inductive /
                            class / axiom / opaque / notation / macro / syntax /
                            variable / universe / open / namespace / section /
                            end / set_option / attribute / import / example /
                            #eval / #exit / unknown commands ...
  * every locked lemma also records a "context hash": the ordered chain of all
    non-lemma commands preceding it, so moving a lemma across a definition,
    `open`, `notation`, `set_option`, ... is detected.

The guard is FAIL-CLOSED: anything it cannot parse confidently (unterminated
comment/string, unbalanced brackets, `end` that matches nothing, a declaration
with no top-level `:=`) is an error or is frozen in full -- never a silent pass.

What it still is NOT
--------------------
A text-level guard.  It does not elaborate Lean, so it cannot see changes in
imported modules outside the guarded directories, in the toolchain/lakefile,
or in the meaning of a name via instances elsewhere.  It is also not
write-protection: whoever can edit the lock file can re-baseline.  Use
`--baseline-ref` (lock read from git, e.g. origin/main) in CI, and keep the
lock file under CODEOWNERS / read-only for the agent.  Completeness of proofs
(no `sorry`, `#print axioms`) is a separate audit.

Exit codes: 0 ok, 1 guard failure / unparsable input, 2 usage error.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import NamedTuple, Optional

LOCK_VERSION = 2
DEFAULT_DIRS = ["BosonizeStubs"]
DEFAULT_LOCK = "docs/spec/stub_locks.v2.json"
DEFAULT_LEGACY_LOCK = "docs/spec/stub_locks.json"

# --------------------------------------------------------------------------- #
# Lexing: remove comments, protect literals
# --------------------------------------------------------------------------- #


class LeanScanError(Exception):
    """Input the guard cannot parse with confidence (treated as a failure)."""


def _is_idch(c: str) -> bool:
    return c.isalnum() or c in "_'!?"


_CHAR_RE = re.compile(
    r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{?[0-9a-fA-F]+\}?|.)|[^\\'\n])'"
)
_RAW_RE = re.compile(r'r(#*)"')


def strip_lean(src: str) -> tuple[str, list[bool]]:
    """Return (clean, litmask).

    Comments (`--`, nested `/- -/`, doc comments) become a space (newlines are
    kept so line numbers stay valid).  String / raw-string / char literals are
    kept verbatim and flagged in `litmask`, so brackets, `:=`, keywords and
    comment openers inside them are never interpreted.
    """
    out: list[str] = []
    lit: list[bool] = []
    i, n = 0, len(src)

    def put(s: str, is_lit: bool = False) -> None:
        out.append(s)
        lit.extend([is_lit] * len(s))

    while i < n:
        c = src[i]
        if c == "/" and src.startswith("/-", i):
            depth, j, nl = 1, i + 2, 0
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    nl += src[j] == "\n"
                    j += 1
            if depth:
                raise LeanScanError(
                    f"unterminated block comment starting on line {src.count(chr(10), 0, i) + 1}"
                )
            put(" " + "\n" * nl)
            i = j
        elif c == "-" and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j  # keep the newline itself
            put(" ")
        elif c == "r" and (i == 0 or not _is_idch(src[i - 1])) and _RAW_RE.match(src, i):
            m = _RAW_RE.match(src, i)
            closer = '"' + m.group(1)
            j = src.find(closer, m.end())
            if j < 0:
                raise LeanScanError(f"unterminated raw string on line {src.count(chr(10), 0, i) + 1}")
            put(src[i : j + len(closer)], True)
            i = j + len(closer)
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            if j >= n:
                raise LeanScanError(f"unterminated string on line {src.count(chr(10), 0, i) + 1}")
            put(src[i : j + 1], True)
            i = j + 1
        elif c == "'" and (i == 0 or not _is_idch(src[i - 1])) and _CHAR_RE.match(src, i):
            m = _CHAR_RE.match(src, i)
            put(m.group(), True)
            i = m.end()
        else:
            put(c)
            i += 1
    return "".join(out), lit


# --------------------------------------------------------------------------- #
# Tokens
# --------------------------------------------------------------------------- #

_IDPART = r"(?:[^\W\d]|«[^»]*»)(?:[\w'!?]|«[^»]*»)*"
_TOKEN_RE = re.compile(rf"{_IDPART}(?:\.{_IDPART})*|\d+(?:\.\d+)?|:=|\S")

OPEN = set("([{⟨⦃⟦")
CLOSE = set(")]}⟩⦄⟧")
BRACKET_PAIRS = dict(zip("([{⟨⦃⟦", ")]}⟩⦄⟧"))


class Tok(NamedTuple):
    kind: str  # 'id' | 'lit' | 'sym' | 'num'
    text: str
    start: int
    end: int
    col: int
    first: bool  # first token on its (cleaned) line


def tokenize(clean: str, mask: list[bool]) -> list[Tok]:
    toks: list[Tok] = []
    i, n = 0, len(clean)
    while i < n:
        if mask[i]:
            j = i
            while j < n and mask[j]:
                j += 1
            kind, text = "lit", clean[i:j]
        elif clean[i].isspace():
            i += 1
            continue
        else:
            m = _TOKEN_RE.match(clean, i)
            j = m.end()
            for k in range(i, j):  # never swallow a literal
                if mask[k]:
                    j = k
                    break
            text = clean[i:j]
            kind = "id" if (text[0].isalpha() or text[0] in "_«") else ("num" if text[0].isdigit() else "sym")
        ls = clean.rfind("\n", 0, i) + 1
        toks.append(Tok(kind, text, i, j, i - ls, clean[ls:i].strip() == ""))
        i = j
    return toks


# --------------------------------------------------------------------------- #
# Command splitting
# --------------------------------------------------------------------------- #

# Reserved words that can only start a command, wherever they appear.
CMD_KW = {
    "import", "prelude", "namespace", "section", "end", "mutual", "universe", "variable",
    "theorem", "lemma", "def", "abbrev", "instance", "example", "axiom", "opaque",
    "structure", "inductive", "coinductive", "class", "attribute", "export", "alias",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "macro", "macro_rules",
    "syntax", "elab", "elab_rules", "declare_syntax_cat", "initialize", "builtin_initialize",
    "run_cmd", "run_meta", "include", "omit", "compile_inductive", "add_decl_doc",
    "assert_not_exists", "suppress_compilation", "register_option", "register_simp_attr",
    "irreducible_def", "lemma_alias", "set_option_alias",
}
# `open` / `set_option` / `in`-prefixes also occur as tactics; only a command if
# they are at column 0, or indented but not ending in `in`.
SOFT_KW = {"open", "set_option"}
IN_PREFIX_KW = {"open", "set_option", "omit", "include"}
MODS = {"private", "protected", "noncomputable", "unsafe", "partial", "nonrec", "local", "scoped"}
# Column-0 tokens that continue the previous command instead of starting one.
CONT = {"where", "termination_by", "decreasing_by", "deriving", "with", "by", "fun",
        "from", "then", "else", "_", "calc", "at", "in"}
DECL_KINDS = {"def", "abbrev", "instance", "structure", "inductive", "class", "axiom", "opaque",
              "irreducible_def"}
# `#`-commands that cannot change the environment.  Anything else (#eval, #exit,
# #guard_msgs, ...) is frozen like any other command.
HARMLESS_HASH = {"#check", "#print", "#reduce", "#synth", "#help", "#where", "#check_failure"}


def _line_end_token(toks: list[Tok], idx: int) -> str:
    j = idx + 1
    while j < len(toks) and not toks[j].first:
        j += 1
    return toks[j - 1].text


def _in_list_position(toks: list[Tok], idx: int) -> bool:
    """`attribute [instance] foo`, `@[simp, instance]`, `[local instance]` ..."""
    p = toks[idx - 1].text if idx >= 1 else ""
    pp = toks[idx - 2].text if idx >= 2 else ""
    return p in ("[", ",") or (p in ("local", "scoped") and pp == "[")


def _match_open(toks: list[Tok], close_idx: int) -> Optional[int]:
    depth = 0
    for k in range(close_idx, -1, -1):
        if toks[k].kind == "lit":
            continue
        if toks[k].text == "]":
            depth += 1
        elif toks[k].text == "[":
            depth -= 1
            if depth == 0:
                return k
    return None


def _extend_back(toks: list[Tok], s: int) -> int:
    """Pull modifiers, `@[..]` blocks and `open .. in` lines into the command."""
    changed = True
    while changed:
        changed = False
        while s > 0 and toks[s - 1].kind == "id" and toks[s - 1].text in MODS:
            s -= 1
            changed = True
        if s > 0 and toks[s - 1].text == "]":
            o = _match_open(toks, s - 1)
            if o is not None and o > 0 and toks[o - 1].text == "@":
                s = o - 1
                changed = True
        if s > 0 and toks[s - 1].text == "deriving" and toks[s].text == "instance":
            s -= 1
            changed = True
        if s > 0 and toks[s - 1].text == "in":
            j = s - 1
            while j > 0 and not toks[j].first:
                j -= 1
            if toks[j].text in IN_PREFIX_KW:
                s = j
                changed = True
    return s


def find_starts(toks: list[Tok]) -> list[int]:
    starts: set[int] = set()
    depth = 0
    for idx, t in enumerate(toks):
        if t.kind == "lit":
            continue
        if t.text in OPEN:
            depth += 1
        elif t.text in CLOSE:
            depth = max(0, depth - 1)
        if t.kind == "id" and t.text in CMD_KW and not _in_list_position(toks, idx):
            starts.add(_extend_back(toks, idx))
            depth = 0
        elif t.kind == "id" and t.text in SOFT_KW and t.first:
            if t.col == 0 or _line_end_token(toks, idx) != "in":
                starts.add(_extend_back(toks, idx))
                depth = 0
        elif t.first and t.col == 0 and depth == 0:
            generic = (
                (t.kind == "id" and t.text not in CONT)
                or (t.text == "#" and idx + 1 < len(toks) and toks[idx + 1].kind == "id"
                    and toks[idx + 1].start == t.end)
                or (t.text == "@" and idx + 1 < len(toks) and toks[idx + 1].text == "[")
            )
            if generic:
                starts.add(_extend_back(toks, idx))
                depth = 0
    return sorted(starts)


# --------------------------------------------------------------------------- #
# Normalisation
# --------------------------------------------------------------------------- #


def collapse_ws(clean: str, mask: list[bool], a: int, b: int) -> str:
    """Whitespace-insensitive form (used for lemma headers)."""
    out: list[str] = []
    prev_space = True
    for i in range(a, b):
        ch = clean[i]
        if mask[i]:
            out.append(ch)
            prev_space = False
        elif ch.isspace():
            if not prev_space:
                out.append(" ")
                prev_space = True
        else:
            out.append(ch)
            prev_space = False
    return "".join(out).strip()


def keep_layout(clean: str, mask: list[bool], a: int, b: int) -> str:
    """Comment-insensitive but layout-sensitive form (used for frozen commands:
    newlines and indentation are kept, trailing blanks / blank lines dropped)."""
    out: list[str] = []
    i = a
    while i < b:
        if mask[i] or not clean[i].isspace():
            out.append(clean[i])
            i += 1
            continue
        j = i
        while j < b and clean[j].isspace() and not mask[j]:
            j += 1
        run = clean[i:j]
        if i == a or j >= b:
            pass
        elif "\n" in run:
            out.append("\n" + run.rsplit("\n", 1)[1])
        else:
            out.append(" ")
        i = j
    return "".join(out)


def sha(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------- #
# File model
# --------------------------------------------------------------------------- #


@dataclass
class Cmd:
    kind: str
    label: str
    hash: str
    text: str
    line: int = 0

    def to_json(self) -> dict:
        return {"kind": self.kind, "label": self.label, "hash": self.hash, "text": self.text}


@dataclass
class Lem:
    kind: str
    hash: str
    ctx: str
    text: str
    line: int = 0
    whole: bool = False  # no top-level `:=` found -> whole declaration frozen

    def to_json(self) -> dict:
        d = {"kind": self.kind, "hash": self.hash, "ctx": self.ctx, "text": self.text}
        if self.whole:
            d["whole"] = True
        return d


@dataclass
class FileModel:
    commands: list[Cmd] = field(default_factory=list)
    lemmas: dict[str, Lem] = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)

    def to_json(self) -> dict:
        return {
            "commands": [c.to_json() for c in self.commands],
            "lemmas": {k: v.to_json() for k, v in sorted(self.lemmas.items())},
        }


def _find_header_end(ctoks: list[Tok], start: int) -> Optional[int]:
    """Index of the token that ends the signature (`:=` / `where`) at bracket
    depth 0, honouring `let x := ..;` / `have h : T := ..` inside the type."""
    depth, pending = 0, 0
    for k in range(start, len(ctoks)):
        t = ctoks[k]
        if t.kind == "lit":
            continue
        if t.text in OPEN:
            depth += 1
        elif t.text in CLOSE:
            depth -= 1
            if depth < 0:
                raise LeanScanError(f"unbalanced '{t.text}' in a declaration header")
        elif t.kind == "id" and t.text in ("let", "have", "letI", "haveI", "let_fun", "suffices"):
            pending += 1
        elif t.text == ":=":
            if pending > 0:
                pending -= 1
            elif depth == 0:
                return k
        elif t.kind == "id" and t.text == "where" and depth == 0 and pending == 0:
            return k
    return None


def parse_lean(text: str) -> FileModel:
    clean, mask = strip_lean(text)
    toks = tokenize(clean, mask)
    # Validate the whole file, including unfrozen proof bodies. Command splitting
    # resets its depth at boundaries and cannot detect malformed nesting itself.
    brackets: list[Tok] = []
    for token in toks:
        if token.kind == "lit":
            continue
        if token.text in OPEN:
            brackets.append(token)
        elif token.text in CLOSE:
            if not brackets or BRACKET_PAIRS[brackets[-1].text] != token.text:
                raise LeanScanError(f"unmatched or mismatched closing bracket '{token.text}'")
            brackets.pop()
    if brackets:
        raise LeanScanError(f"unclosed bracket '{brackets[-1].text}'")
    model = FileModel()
    if not toks:
        return model

    def line_of(off: int) -> int:
        return clean.count("\n", 0, off) + 1

    starts = find_starts(toks)
    has_preamble = not starts or starts[0] != 0
    bounds = ([0] if has_preamble else []) + starts
    stack: list[tuple[str, Optional[str]]] = []
    ctx = sha("")

    for bi, a in enumerate(bounds):
        b = bounds[bi + 1] if bi + 1 < len(bounds) else len(toks)
        ctoks = toks[a:b]
        kwi = next(
            (i for i, t in enumerate(ctoks) if t.kind == "id" and t.text in CMD_KW
             and not _in_list_position(toks, a + i)),
            None,
        )
        if has_preamble and bi == 0:
            kind = "<preamble>"
        elif kwi is not None:
            kind = ctoks[kwi].text
        elif ctoks[0].text == "#" and len(ctoks) > 1:
            kind = "#" + ctoks[1].text
        else:
            kind = ctoks[0].text
        if kind in HARMLESS_HASH:
            continue

        s, e = ctoks[0].start, ctoks[-1].end
        line = line_of(s)
        qprefix = ".".join(n for k, n in stack if k == "namespace" and n)

        if kind in ("theorem", "lemma"):
            if kwi is None or kwi + 1 >= len(ctoks) or ctoks[kwi + 1].kind != "id":
                raise LeanScanError(f"line {line}: cannot read the name of this {kind}")
            name = ctoks[kwi + 1].text
            if name.startswith("_root_."):
                qname = name[len("_root_."):]
            else:
                qname = f"{qprefix}.{name}" if qprefix else name
            hend = _find_header_end(ctoks, kwi + 2)
            whole = hend is None
            end_off = e if whole else ctoks[hend].start
            if whole:
                model.notes.append(
                    f"line {line}: `{qname}` has no top-level `:=`/`where`; its whole text is frozen"
                )
            header = collapse_ws(clean, mask, s, end_off)
            if qname in model.lemmas:
                raise LeanScanError(f"line {line}: duplicate declaration name `{qname}`")
            model.lemmas[qname] = Lem(kind, sha(header), ctx, header, line, whole)
            continue

        body = keep_layout(clean, mask, s, e)
        if kwi is not None and kwi + 1 < len(ctoks) and ctoks[kwi + 1].kind == "id":
            nm = ctoks[kwi + 1].text
            if qprefix and kind in DECL_KINDS:
                nm = f"{qprefix}.{nm}"
            label = f"{kind} {nm}"
        else:
            label = f"{kind} {body.split(chr(10))[0][len(kind):].strip()[:40]}".strip()

        if kind in ("namespace", "section", "mutual"):
            nm = ctoks[kwi + 1].text if kwi is not None and kwi + 1 < len(ctoks) and kind != "mutual" else None
            if kind == "namespace" and nm is None:
                raise LeanScanError(f"line {line}: `namespace` without a name")
            stack.append((kind, nm))
        elif kind == "end":
            nm = ctoks[kwi + 1].text if kwi is not None and kwi + 1 < len(ctoks) else None
            if not stack:
                raise LeanScanError(f"line {line}: `end` closes nothing")
            _, open_name = stack.pop()
            if nm != open_name:
                raise LeanScanError(
                    f"line {line}: `end {nm or ''}` does not match the open `{open_name or '(unnamed)'}`"
                )

        h = sha(body)
        model.commands.append(Cmd(kind, label, h, body, line))
        ctx = sha(ctx + h)
    return model


# --------------------------------------------------------------------------- #
# Whole-tree extraction, baseline I/O
# --------------------------------------------------------------------------- #


def lean_files(root: Path, dirs: list[str]) -> list[Path]:
    found: set[Path] = set()
    for d in dirs:
        base = root / d
        if base.is_file() and base.suffix == ".lean":
            found.add(base)
        elif base.is_dir():
            found.update(p for p in base.rglob("*.lean") if p.is_file())
    return sorted(found)


def extract(root: Path, dirs: list[str]) -> tuple[dict[str, FileModel], list[str]]:
    models: dict[str, FileModel] = {}
    errors: list[str] = []
    for p in lean_files(root, dirs):
        key = p.relative_to(root).as_posix()
        try:
            models[key] = parse_lean(p.read_text(encoding="utf-8"))
        except LeanScanError as e:
            errors.append(f"{key}: UNPARSABLE ({e}) -- refusing to guess")
        except UnicodeDecodeError as e:
            errors.append(f"{key}: not valid UTF-8 ({e})")
    return models, errors


def to_baseline(models: dict[str, FileModel]) -> dict:
    return {"version": LOCK_VERSION, "files": {k: m.to_json() for k, m in sorted(models.items())}}


def load_baseline_file(path: Path) -> dict:
    return _validate_baseline(json.loads(path.read_text(encoding="utf-8")), str(path))


def load_baseline_ref(root: Path, ref: str, lock: str) -> dict:
    r = subprocess.run(["git", "-C", str(root), "show", f"{ref}:{lock}"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"[stub_lock] cannot read {lock} at git ref '{ref}': {r.stderr.strip()}")
    return _validate_baseline(json.loads(r.stdout), f"{ref}:{lock}")


def _validate_baseline(data: dict, where: str) -> dict:
    if not isinstance(data, dict) or data.get("version") != LOCK_VERSION or "files" not in data:
        raise SystemExit(
            f"[stub_lock] {where} is not a version-{LOCK_VERSION} lock file. "
            "Regenerate it (see --legacy-check, then --update)."
        )
    return data


# --------------------------------------------------------------------------- #
# Comparison
# --------------------------------------------------------------------------- #


def word_diff(old: str, new: str) -> str:
    a, b = old.split(), new.split()
    out: list[str] = []
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes():
        if op == "equal":
            seg = a[i1:i2]
            out.append(" ".join(seg if len(seg) <= 8 else seg[:3] + ["..."] + seg[-3:]))
            continue
        if i2 > i1:
            out.append("[-" + " ".join(a[i1:i2]) + "-]")
        if j2 > j1:
            out.append("{+" + " ".join(b[j1:j2]) + "+}")
    return " ".join(out)


def _short(s: str, n: int = 160) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[: n - 3] + "..."


def compare_file(path: str, base: dict, cur: FileModel) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []

    # 1. non-lemma commands: exact ordered sequence
    bcmds = base.get("commands", [])
    bh = [c["hash"] for c in bcmds]
    ch = [c.hash for c in cur.commands]
    seq_ok = bh == ch
    if not seq_ok:
        sm = difflib.SequenceMatcher(a=bh, b=ch, autojunk=False)
        for op, i1, i2, j1, j2 in sm.get_opcodes():
            if op == "equal":
                continue
            for c in bcmds[i1:i2]:
                if op == "delete" or (op == "replace" and (i2 - i1) != (j2 - j1)):
                    errors.append(f"{path}: frozen command removed/changed: `{c['label']}`")
            if op == "replace" and (i2 - i1) == (j2 - j1):
                for old, new in zip(bcmds[i1:i2], cur.commands[j1:j2]):
                    errors.append(
                        f"{path}:{new.line}: frozen command changed: `{old['label']}`\n"
                        f"      {word_diff(' '.join(old['text'].split()), ' '.join(new.text.split()))[:600]}"
                    )
            if op in ("insert", "replace"):
                for c in cur.commands[j1:j2]:
                    errors.append(
                        f"{path}:{c.line}: new/changed non-lemma command not in the baseline: "
                        f"`{c.label}` -> {_short(c.text)}"
                    )

    # 2. locked lemmas
    blem = base.get("lemmas", {})
    for name, b in blem.items():
        c = cur.lemmas.get(name)
        if c is None:
            errors.append(f"{path}: locked declaration `{name}` was removed, renamed or moved to another namespace")
            continue
        if c.hash != b["hash"]:
            errors.append(
                f"{path}:{c.line}: STATEMENT CHANGED: `{name}`\n"
                f"      {word_diff(b['text'], c.text)[:800]}"
            )
        elif seq_ok and c.ctx != b["ctx"]:
            errors.append(
                f"{path}:{c.line}: `{name}` now sits after a different set of definitions/opens/"
                "options than when it was locked (a context command was moved across it)"
            )

    # 3. additions (unreviewed, unlocked)
    for name, c in cur.lemmas.items():
        if name not in blem:
            warnings.append(f"{path}:{c.line}: NEW unlocked {c.kind} `{name}` (needs human review / lock)")
    for n in cur.notes:
        warnings.append(f"{path}: {n}")
    return errors, warnings


def check(root: Path, dirs: list[str], baseline: dict) -> tuple[list[str], list[str]]:
    models, errors = extract(root, dirs)
    warnings: list[str] = []
    for fpath, b in baseline["files"].items():
        if fpath not in models:
            if not any(e.startswith(fpath + ":") for e in errors):
                errors.append(f"{fpath}: locked file is missing from disk")
            continue
        e, w = compare_file(fpath, b, models[fpath])
        errors += e
        warnings += w
    for fpath, m in models.items():
        if fpath not in baseline["files"]:
            warnings.append(
                f"{fpath}: NEW file not in the baseline ({len(m.lemmas)} unlocked lemma(s), "
                f"{len(m.commands)} unfrozen command(s))"
            )
    return errors, warnings


# --------------------------------------------------------------------------- #
# Legacy (v1) cross-check: lets you verify the v2 baseline starts from exactly
# the text that was approved under the old guard.
# --------------------------------------------------------------------------- #

_LEGACY_RE = re.compile(
    r"(?m)^(?P<decl>theorem|lemma)\s+(?P<name>[a-zA-Z0-9_'.]+)(?P<sig>[\s\S]*?)(?::=|\n\s*:=)"
)


def legacy_extract(root: Path, dirs: list[str]) -> dict[str, dict[str, str]]:
    out: dict[str, dict[str, str]] = {}
    for p in lean_files(root, dirs):
        sigs: dict[str, str] = {}
        for m in _LEGACY_RE.finditer(p.read_text(encoding="utf-8")):
            norm = f"{m.group('decl')} {m.group('name')} {' '.join(m.group('sig').split())}".strip()
            sigs[m.group("name")] = hashlib.sha256(norm.encode("utf-8")).hexdigest()
        if sigs:
            out[p.relative_to(root).as_posix()] = sigs
    return out


def legacy_check(root: Path, dirs: list[str], lock: Path) -> int:
    old = json.loads(lock.read_text(encoding="utf-8"))
    cur = legacy_extract(root, dirs)
    bad = 0
    for f, decls in old.items():
        for name, h in decls.items():
            if cur.get(f, {}).get(name) != h:
                print(f"[stub_lock] legacy mismatch: {f}: {name}", file=sys.stderr)
                bad += 1
    if bad:
        print(f"[stub_lock] legacy check FAILED ({bad}); do NOT re-baseline.", file=sys.stderr)
        return 1
    n = sum(len(d) for d in old.values())
    print(f"[stub_lock] legacy check PASSED: current text matches all {n} previously approved signatures.")
    return 0


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def _print_list(title: str, items: list[str], stream) -> None:
    print(f"[stub_lock] {title}", file=stream)
    for it in items:
        print(f"  - {it}", file=stream)


def cmd_report(root: Path, dirs: list[str]) -> int:
    models, errors = extract(root, dirs)
    for k, m in sorted(models.items()):
        print(f"{k}: {len(m.lemmas)} locked-header declaration(s), {len(m.commands)} fully-frozen command(s)")
        for c in m.commands:
            print(f"    frozen  line {c.line:>4}  {c.label}")
        for n, l in m.lemmas.items():
            print(f"    header  line {l.line:>4}  {l.kind} {n}{'  [WHOLE TEXT FROZEN]' if l.whole else ''}")
    if errors:
        _print_list("UNPARSABLE:", errors, sys.stderr)
        return 1
    return 0


def cmd_update(root: Path, dirs: list[str], lock: Path, accept: bool) -> int:
    if os.environ.get("CI"):
        print("[stub_lock] --update is disabled when $CI is set.", file=sys.stderr)
        return 1
    models, errors = extract(root, dirs)
    if errors:
        _print_list("cannot lock, unparsable input:", errors, sys.stderr)
        return 1
    if lock.exists():
        try:
            old = load_baseline_file(lock)
        except SystemExit as e:
            print(e, file=sys.stderr)
            return 1
        errs, _ = check(root, dirs, old)
        if errs and not accept:
            _print_list("refusing to overwrite: this would change already-locked content:", errs, sys.stderr)
            print("[stub_lock] If a human reviewed every item above, re-run with --accept-changes.",
                  file=sys.stderr)
            return 1
        if errs:
            _print_list("ACCEPTING these changes to locked content:", errs, sys.stderr)
    lock.parent.mkdir(parents=True, exist_ok=True)
    lock.write_text(json.dumps(to_baseline(models), indent=2, sort_keys=True, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    nl = sum(len(m.lemmas) for m in models.values())
    nc = sum(len(m.commands) for m in models.values())
    print(f"[stub_lock] Locked {nl} declaration header(s) and {nc} frozen command(s) "
          f"across {len(models)} file(s) into {lock}.")
    return 0


def cmd_check(root: Path, dirs: list[str], lock: Path, lock_rel: str, ref: Optional[str], strict: bool) -> int:
    warnings: list[str] = []
    if ref:
        baseline = load_baseline_ref(root, ref, lock_rel)
        if lock.exists() and json.loads(lock.read_text(encoding="utf-8")) != baseline:
            warnings.append(f"{lock_rel} differs from its version at {ref} (baseline was changed in this branch)")
    else:
        if not lock.exists():
            print(f"[stub_lock] Lock file '{lock}' not found. Run --update after human review.", file=sys.stderr)
            return 1
        baseline = load_baseline_file(lock)
    errors, w = check(root, dirs, baseline)
    warnings += w
    if strict:
        errors += [f"(strict) {x}" for x in warnings]
        warnings = []
    if warnings:
        _print_list("warnings:", warnings, sys.stderr)
    if errors:
        _print_list("Verification FAILED:", errors, sys.stderr)
        return 1
    nl = sum(len(f["lemmas"]) for f in baseline["files"].values())
    nc = sum(len(f["commands"]) for f in baseline["files"].values())
    print(f"[stub_lock] Verification PASSED: {nl} statement(s) and {nc} frozen command(s) verified.")
    return 0


def main(argv: Optional[list[str]] = None) -> int:
    ap = argparse.ArgumentParser(description="Statement-freeze guard for Lean staging files.")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true", help="verify against the lock")
    g.add_argument("--update", action="store_true", help="write the lock (human-reviewed state only)")
    g.add_argument("--legacy-check", action="store_true", help="verify against the old v1 lock (migration aid)")
    g.add_argument("--report", action="store_true", help="show exactly what would be frozen")
    ap.add_argument("--strict", action="store_true", help="treat warnings (new lemmas/files) as errors")
    ap.add_argument("--accept-changes", action="store_true", help="--update may overwrite changed locked content")
    ap.add_argument("--baseline-ref", metavar="GITREF", help="read the lock from this git ref instead of the working tree")
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    ap.add_argument("--dir", action="append", dest="dirs", help="guarded directory (repeatable; default BosonizeStubs)")
    ap.add_argument("--lock-file", default=DEFAULT_LOCK)
    ap.add_argument("--legacy-lock", default=DEFAULT_LEGACY_LOCK)
    a = ap.parse_args(argv)

    root = Path(a.root).resolve()
    dirs = a.dirs or DEFAULT_DIRS
    lock = root / a.lock_file
    try:
        if a.report:
            return cmd_report(root, dirs)
        if a.update:
            return cmd_update(root, dirs, lock, a.accept_changes)
        if a.legacy_check:
            return legacy_check(root, dirs, root / a.legacy_lock)
        return cmd_check(root, dirs, lock, a.lock_file, a.baseline_ref, a.strict)
    except LeanScanError as e:  # pragma: no cover
        print(f"[stub_lock] unparsable input: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
