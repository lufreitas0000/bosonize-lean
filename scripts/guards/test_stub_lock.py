#!/usr/bin/env python3
"""Mutation tests for stub_lock.py.  Run:  python3 scripts/guards/test_stub_lock.py"""
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import stub_lock as sl  # noqa: E402

FIXTURE = r'''import Mathlib

namespace Bosonize.Ch01

open Finset

/-- A doc comment mentioning lemma foo : False := by sorry -/
def inBandPredicate (L : ℕ) (k : ℤ) : Prop := -(L : ℤ) < 2 * k ∧ 2 * k ≤ L

noncomputable def quotientMap (L : ℕ) : ℤ → ℤ := fun k => k % L

abbrev Band := ℤ

instance : Inhabited Band := ⟨0⟩

/-- zero is in the band. -/
theorem zero_mem_band (L : ℕ) (hL : 0 < L) : inBandPredicate L 0 := by
  -- a comment with := and theorem and (
  sorry

lemma band_add_comm (L : ℕ) (a b : ℤ) (h : a = b := by simp) :
    a + b = b + a := by
  sorry

@[simp] private lemma attr_one (n : ℕ) : n + 0 = n := by
  sorry

theorem let_stmt : let x := 5; x = 5 := by
  sorry

lemma str_in_sig (s : String := "a := b /- not a comment") : s = s := by sorry

lemma char_in_sig (c : Char := '(') : c = c := by sorry

lemma multi_line_binders
    (a : ℤ)
    (b : ℤ) :
    a + b = b + a := by
  sorry

open Classical in
theorem with_open_prefix (p : Prop) : p ∨ ¬p := by
  sorry

end Bosonize.Ch01
'''

LEMMAS = {"Bosonize.Ch01." + n for n in
          ["zero_mem_band", "band_add_comm", "attr_one", "let_stmt", "str_in_sig",
           "char_in_sig", "multi_line_binders", "with_open_prefix"]}


class Base(unittest.TestCase):
    def setUp(self):
        self._td = tempfile.TemporaryDirectory()
        self.root = Path(self._td.name)
        (self.root / "BosonizeStubs").mkdir()
        self.f = self.root / "BosonizeStubs" / "Ch01LatticeBand.lean"
        self.f.write_text(FIXTURE, encoding="utf-8")
        models, errs = sl.extract(self.root, ["BosonizeStubs"])
        self.assertEqual(errs, [])
        self.baseline = sl.to_baseline(models)

    def tearDown(self):
        self._td.cleanup()

    def mutate(self, old, new, count=1):
        src = FIXTURE
        self.assertIn(old, src, "mutation target not in fixture")
        self.f.write_text(src.replace(old, new, count), encoding="utf-8")

    def run_check(self):
        return sl.check(self.root, ["BosonizeStubs"], self.baseline)

    def assertPass(self, warn=None):
        e, w = self.run_check()
        self.assertEqual(e, [], e)
        if warn is not None:
            self.assertTrue(any(warn in x for x in w), w)

    def assertReject(self, needle=None):
        e, _ = self.run_check()
        self.assertTrue(e, "guard accepted a mutation it must reject")
        if needle:
            self.assertTrue(any(needle in x for x in e), e)


class TestBaseline(Base):
    def test_all_lemmas_found(self):
        m = sl.parse_lean(FIXTURE)
        self.assertEqual(set(m.lemmas), LEMMAS)

    def test_unchanged_passes(self):
        self.assertPass()


class TestAllowedEdits(Base):
    def test_proof_body_change(self):
        self.mutate("  sorry\n\nlemma band_add_comm", "  intro; simp; omega\n\nlemma band_add_comm")
        self.assertPass()

    def test_proof_body_with_comments_and_junk(self):
        self.mutate("  -- a comment with := and theorem and (\n  sorry",
                    "  /- nested /- c -/ := ( -/\n  have h : (1:ℕ) := 1\n  exact (by simpa [\"x\"] using h)")
        self.assertPass()

    def test_doc_comment_and_header_whitespace(self):
        self.mutate("(L : ℕ) (hL : 0 < L) : inBandPredicate L 0 := by",
                    "(L : ℕ)\n   (hL : 0 < L)\n      :   inBandPredicate L 0   :=\n  by")
        self.assertPass()

    def test_comment_inside_header(self):
        self.mutate("(hL : 0 < L)", "(hL : 0 < L) -- harmless\n")
        self.assertPass()

    def test_lemmas_reordered(self):
        a = FIXTURE.index("lemma band_add_comm")
        b = FIXTURE.index("@[simp] private lemma")
        blk = FIXTURE[a:b]
        self.f.write_text(FIXTURE[:a] + FIXTURE[b:].replace("theorem let_stmt", blk + "theorem let_stmt", 1))
        self.assertPass()

    def test_new_lemma_is_warning_not_error(self):
        self.mutate("end Bosonize.Ch01", "lemma helper (n : ℕ) : n = n := rfl\n\nend Bosonize.Ch01")
        self.assertPass(warn="NEW unlocked lemma `Bosonize.Ch01.helper`")

    def test_harmless_hash_commands(self):
        self.mutate("end Bosonize.Ch01", "#check zero_mem_band\n#print axioms zero_mem_band\nend Bosonize.Ch01")
        self.assertPass()


class TestStatementDrift(Base):
    def test_hypothesis_weakened(self):
        self.mutate("(hL : 0 < L)", "(hL : 1 < L)")
        self.assertReject("STATEMENT CHANGED")

    def test_conclusion_changed(self):
        self.mutate("inBandPredicate L 0 := by", "True := by")
        self.assertReject("zero_mem_band")

    def test_hypothesis_dropped(self):
        self.mutate("(hL : 0 < L) : inBandPredicate", " : inBandPredicate")
        self.assertReject()

    def test_declaration_removed(self):
        a = FIXTURE.index("/-- zero is in the band. -/")
        b = FIXTURE.index("lemma band_add_comm")
        self.f.write_text(FIXTURE[:a] + FIXTURE[b:])
        self.assertReject("removed")

    def test_renamed(self):
        self.mutate("theorem zero_mem_band", "theorem zero_mem_band'")
        self.assertReject()

    def test_lemma_to_theorem(self):
        self.mutate("lemma band_add_comm", "theorem band_add_comm")
        self.assertReject()

    def test_attribute_added_or_removed(self):
        self.mutate("@[simp] private lemma", "private lemma")
        self.assertReject("attr_one")

    def test_modifier_added(self):
        self.mutate("theorem zero_mem_band", "protected theorem zero_mem_band")
        self.assertReject()

    def test_change_inside_binder_default_with_assign(self):
        # `:=` inside a binder must not end the header early
        self.mutate("(h : a = b := by simp)", "(h : a = b := by simp) (h2 : False)")
        self.assertReject("band_add_comm")

    def test_change_after_binder_default(self):
        self.mutate("a + b = b + a := by\n  sorry\n\n@[simp]", "a + b = b + b := by\n  sorry\n\n@[simp]")
        self.assertReject("band_add_comm")

    def test_let_in_statement(self):
        self.mutate("let x := 5; x = 5", "let x := 5; x = 6")
        self.assertReject("let_stmt")

    def test_string_default_with_assign_and_comment_opener(self):
        self.mutate('"a := b /- not a comment") : s = s', '"a := b /- not a comment") : s = s ∧ False')
        self.assertReject("str_in_sig")

    def test_char_literal_bracket(self):
        self.mutate("(c : Char := '(') : c = c", "(c : Char := '(') : c ≠ c")
        self.assertReject("char_in_sig")

    def test_comment_cannot_hide_a_change(self):
        # turning the real conclusion into a comment is a change
        self.mutate("a + b = b + a := by\n  sorry\n\n@[simp]", "True -- a + b = b + a\n := by\n  sorry\n\n@[simp]")
        self.assertReject("band_add_comm")

    def test_open_prefix_removed(self):
        self.mutate("open Classical in\ntheorem with_open_prefix", "theorem with_open_prefix")
        self.assertReject()

    def test_inline_namespace_move(self):
        self.mutate("theorem zero_mem_band", "theorem _root_.zero_mem_band")
        self.assertReject()


class TestDefinitionsAndContext(Base):
    def test_def_body_changed(self):
        self.mutate("fun k => k % L", "fun _ => 0")
        self.assertReject("quotientMap")

    def test_def_predicate_changed(self):
        self.mutate("2 * k ≤ L", "True")
        self.assertReject("inBandPredicate")

    def test_namespace_changed(self):
        self.mutate("namespace Bosonize.Ch01", "namespace Bosonize.Other")
        self.assertReject()

    def test_instance_changed(self):
        self.mutate("⟨0⟩", "⟨1⟩")
        self.assertReject("Inhabited")

    def test_open_removed(self):
        self.mutate("open Finset\n", "")
        self.assertReject()

    def test_new_def_rejected(self):
        self.mutate("end Bosonize.Ch01", "def sneaky : Prop := True\n\nend Bosonize.Ch01")
        self.assertReject("sneaky")

    def test_new_axiom_rejected(self):
        self.mutate("end Bosonize.Ch01", "axiom bad : False\n\nend Bosonize.Ch01")
        self.assertReject("bad")

    def test_indented_axiom_hidden_in_proof_body(self):
        self.mutate("  -- a comment with := and theorem and (\n  sorry",
                    "  sorry\n  axiom bad : False")
        self.assertReject("bad")

    def test_indented_def_hidden_in_proof_body(self):
        self.mutate("  -- a comment with := and theorem and (\n  sorry",
                    "  sorry\n    def evil : Prop := True")
        self.assertReject("evil")

    def test_set_option_injected_between_lemmas(self):
        self.mutate("lemma band_add_comm", "set_option autoImplicit true\n\nlemma band_add_comm")
        self.assertReject()

    def test_indented_set_option_between_lemmas(self):
        self.mutate("  sorry\n\nlemma band_add_comm", "  sorry\n  set_option autoImplicit true\n\nlemma band_add_comm")
        self.assertReject()

    def test_set_option_in_tactic_is_ok(self):
        self.mutate("  -- a comment with := and theorem and (\n  sorry",
                    "  set_option maxRecDepth 2000 in\n  simp")
        self.assertPass()

    def test_local_notation_injected(self):
        self.mutate("lemma band_add_comm", "local notation \"X\" => (0:ℤ)\n\nlemma band_add_comm")
        self.assertReject()

    def test_attribute_command_injected(self):
        self.mutate("end Bosonize.Ch01", "attribute [local instance] foo\n\nend Bosonize.Ch01")
        self.assertReject()

    def test_instance_in_attribute_list_is_not_a_boundary(self):
        src = "namespace A\n\nattribute [local instance] foo\n\ntheorem t : True := by\n  trivial\n\nend A\n"
        m = sl.parse_lean(src)
        self.assertEqual([c.kind for c in m.commands], ["namespace", "attribute", "end"])
        self.assertEqual(set(m.lemmas), {"A.t"})

    def test_hash_exit_rejected(self):
        self.mutate("lemma band_add_comm", "#exit\nlemma band_add_comm")
        self.assertReject()

    def test_hash_eval_rejected(self):
        self.mutate("end Bosonize.Ch01", "#eval 1\nend Bosonize.Ch01")
        self.assertReject()

    def test_lemma_moved_across_definition(self):
        a = FIXTURE.index("/-- zero is in the band. -/")
        b = FIXTURE.index("lemma band_add_comm")
        blk = FIXTURE[a:b]
        s = FIXTURE[:a] + FIXTURE[b:]
        s = s.replace("noncomputable def quotientMap", blk + "noncomputable def quotientMap", 1)
        self.f.write_text(s)
        self.assertReject("different set of definitions")

    def test_unbalanced_end(self):
        self.mutate("end Bosonize.Ch01", "end Bosonize.Wrong")
        self.assertReject()

    def test_unterminated_comment_fails_closed(self):
        self.f.write_text(FIXTURE + "\n/- oops")
        e, _ = self.run_check()
        self.assertTrue(any("UNPARSABLE" in x for x in e), e)

    def test_unterminated_string_fails_closed(self):
        self.f.write_text(FIXTURE + '\ndef s := "oops\n')
        e, _ = self.run_check()
        self.assertTrue(any("UNPARSABLE" in x for x in e), e)

    def test_unclosed_bracket_in_proof_fails_closed(self):
        self.mutate("  -- a comment with := and theorem and (\n  sorry", "  sorry\n  (")
        self.assertReject("UNPARSABLE")

    def test_mismatched_bracket_in_proof_fails_closed(self):
        self.mutate("  -- a comment with := and theorem and (\n  sorry", "  sorry\n  ([)]")
        self.assertReject("UNPARSABLE")

    def test_extra_closing_bracket_fails_closed(self):
        self.f.write_text(FIXTURE + "\n)")
        self.assertReject("UNPARSABLE")

    def test_deleted_file(self):
        self.f.unlink()
        self.assertReject("missing")

    def test_new_file_is_warning(self):
        (self.root / "BosonizeStubs" / "Ch02.lean").write_text("theorem x : True := trivial\n")
        self.assertPass(warn="NEW file")

    def test_duplicate_names_fail_closed(self):
        self.f.write_text(FIXTURE.replace("end Bosonize.Ch01",
                                          "theorem zero_mem_band : True := trivial\nend Bosonize.Ch01"))
        e, _ = self.run_check()
        self.assertTrue(any("UNPARSABLE" in x and "duplicate" in x for x in e), e)

    def test_no_assign_freezes_whole_decl(self):
        src = "theorem eqn : ∀ n : ℕ, n = n\n  | 0 => rfl\n  | n+1 => rfl\n"
        m = sl.parse_lean(src)
        self.assertTrue(m.lemmas["eqn"].whole)
        m2 = sl.parse_lean(src.replace("rfl\n  | n+1", "rfl'\n  | n+1"))
        self.assertNotEqual(m.lemmas["eqn"].hash, m2.lemmas["eqn"].hash)


class TestCLI(Base):
    def cli(self, *args, env=None):
        e = dict(os.environ)
        e.pop("CI", None)
        e.update(env or {})
        return subprocess.run([sys.executable, str(Path(sl.__file__)), "--root", str(self.root), *args],
                              capture_output=True, text=True, env=e)

    def test_update_check_roundtrip(self):
        r = self.cli("--update")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(self.cli("--check").returncode, 0)
        self.mutate("(hL : 0 < L)", "(hL : 1 < L)")
        r = self.cli("--check")
        self.assertEqual(r.returncode, 1)
        self.assertIn("STATEMENT CHANGED", r.stderr)

    def test_update_refuses_to_launder_a_change(self):
        self.cli("--update")
        self.mutate("(hL : 0 < L)", "(hL : 1 < L)")
        r = self.cli("--update")
        self.assertEqual(r.returncode, 1)
        self.assertEqual(self.cli("--check").returncode, 1)  # lock untouched
        r = self.cli("--update", "--accept-changes")
        self.assertEqual(r.returncode, 0)
        self.assertEqual(self.cli("--check").returncode, 0)

    def test_update_disabled_in_ci(self):
        self.assertEqual(self.cli("--update", env={"CI": "true"}).returncode, 1)

    def test_strict_fails_on_new_lemma(self):
        self.cli("--update")
        self.mutate("end Bosonize.Ch01", "lemma helper (n : ℕ) : n = n := rfl\n\nend Bosonize.Ch01")
        self.assertEqual(self.cli("--check").returncode, 0)
        self.assertEqual(self.cli("--check", "--strict").returncode, 1)

    def test_baseline_ref_defeats_lock_tampering(self):
        git = lambda *a: subprocess.run(["git", "-C", str(self.root), *a], check=True, capture_output=True)
        self.cli("--update")
        git("init", "-q")
        git("-c", "user.email=a@b", "-c", "user.name=t", "add", "-A")
        git("-c", "user.email=a@b", "-c", "user.name=t", "commit", "-qm", "base")
        git("branch", "-M", "main")
        # agent edits the statement AND re-baselines the working-tree lock
        self.mutate("(hL : 0 < L)", "(hL : 1 < L)")
        self.assertEqual(self.cli("--update", "--accept-changes").returncode, 0)
        self.assertEqual(self.cli("--check").returncode, 0)  # fooled without a ref ...
        r = self.cli("--check", "--baseline-ref", "main")      # ... but not with one
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("STATEMENT CHANGED", r.stderr)

    def test_legacy_check(self):
        import hashlib
        src = self.f.read_text()
        old = sl.legacy_extract(self.root, ["BosonizeStubs"])
        (self.root / "docs" / "spec").mkdir(parents=True)
        (self.root / "docs" / "spec" / "stub_locks.json").write_text(json.dumps(old))
        self.assertEqual(self.cli("--legacy-check").returncode, 0)
        self.mutate("(hL : 0 < L)", "(hL : 1 < L)")
        self.assertEqual(self.cli("--legacy-check").returncode, 1)


if __name__ == "__main__":
    unittest.main(verbosity=1)
