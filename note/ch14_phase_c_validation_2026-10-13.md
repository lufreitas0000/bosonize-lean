# CH14 / finite-exponential A05 Phase C verification — 2026-10-13

The approved Phase B checkpoint is `339b4c0`. The exact source migration preserves all mathematical declarations and proof bodies: A05 moves byte-identically, and CH14 changes only its reviewed staging-to-Core import. Independent migration review and the machine-readable delta are retained. Existing 21 Core source hashes are unchanged; the manifest now freezes 23 modules and 793 proved statements.

Fresh current-checkout builds of both libraries pass 3410 jobs with no errors or warnings. A warning-as-error audit through the Core aggregator covers all 152 declarations from CH13/multispecies A05 and CH14/finite-exponential A05: 90 theorem proofs and 62 data declarations. Every dependency uses only the permitted standard axioms or none; no sorryAx occurs. See project_sync_axiom_audit_2026-10-13.json for exact hashes and outputs.

Native Core diagnostics complete successfully for all four modules, without warnings, errors, timeouts or failed dependencies. CH13 retains one informational tactic suggestion, which is not a warning or failed proof. All four sources have no placeholders. Strict interface checks pass 793 statements and 632 commands; full CI is run against the committed migration checkpoint and its final result is recorded below.

The independently reviewed CH14 and A05 lecture hashes still match ch14_phase_c_pedagogical_review_2026-10-12.md, preserving the original reference exposition and formulas. The moved formal companions now link to actual Core files, state their current verified status, and retain draft history. KaTeX 0.16.22 validates 321 mathematical fragments in CH13, CH14 and A05 with no errors.

Verified scope: generic finite Taylor identities and inverses under actual nilpotency; actual ambient/subtype phase nilpotency; true typed adjoints and explicit holonomy; full retained physical ground expansion; exact projection excursions; and the conditional cyclic/common-residual field comparison. This does not prove an unconditional finite field–vertex dictionary, and no analytic exponential or unqualified physical equality is claimed.

CH13 and its multispecies A05 support remain complete through all A–B–C phases with unchanged frozen Core hashes. The broader appendix retains research proposals outside these implemented finite portions. Git/GitHub synchronization follows CI; subsequent chapters are not started by this verification task.
