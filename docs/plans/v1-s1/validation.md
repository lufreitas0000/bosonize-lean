# V1-S1 accepted local validation — 2026-10-17

Phase C complete. This receipt covers the uncompressed oscillator sprint only.

- Compiler: Lean 4.35.0-rc4, commit c29b6dda4f7c20e3eeaa717c4e565663c5cfa364.
- Main Core SHA-256: f26d52cb29008f7d39030157368b7b9131bf14a4db173e97ef404062220852a9.
- Helper Core SHA-256: 33fefe1fafbdde6c544925a641ac8cdec496ce571f3036558500a53ddb0ddeff.
- Interface manifest: e9e1682040cbbed0f8eb9ddd42a65b59f50afbd14b62b1dfbebcb6d6499712d6.
- Core manifest: cbe522f531b1bb0b0ac6950527b01ca2bfff32976a833c4898b68584f7c280af.
- `lake build Bosonize BosonizeStubs`: PASS, 3423 jobs for the combined build;
  accepted sources have zero warnings and zero placeholders.
- `make lock-check`: PASS, 1114 statements/1126 frozen commands and 36 Core
  sources. All 34 prior Core hashes and all unrelated interface entries preserved.
- `lake env lean docs/plans/v1-s1/axiom-audit.lean`: PASS, 57 new declarations
  and 14 A08 dependencies. Only propext, Classical.choice, Quot.sound.
  [Exact output](axiom-audit.txt); no sorryAx or additional trusted axioms.
- `make ci`: PASS. [Full output](ci-output.txt) (trailing whitespace normalized): 69 guard tests, both library
  builds, 18 Web-LLM/verifier tests, CI OK. Its deliberate `Fixture.value`
  sorryAx validates rejection behavior; accepted S1 sources have no sorryAx.
- Independent reviewer `/root/s1_interface_review`: PASS for initial interface,
  scoped helper/import amendment, completed proof, actual migration and pedagogy.
  Exact reviewed hashes and resolved findings are in the
  [Core companion](../../companion/Bosonize/Core/V1S1OrderedWick.md).

The earlier quota checkpoint misread usedPercent; it is corrected. The normal
allowance was available and no reset credit was used. No paid-provider calls,
push, external publication, S2 work or broader project completion is claimed.
