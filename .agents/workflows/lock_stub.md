# /lock_stub

**Description:** Transitions a chapter from Phase A (Staging) to Phase B (Interactive Proof Search) after Human-in-the-Loop approval.

**Instructions for the Agent:**
When the user invokes `/lock_stub <Chapter Number>` (e.g., `/lock_stub 1`), execute the following steps:

1. **Acknowledge Approval:** Acknowledge that the definitions, margin constraints, and theorem signatures in `BosonizeStubs/ChNN.lean` have been mathematically validated by the human architect.
2. **Lock Signatures:** If you have terminal access, execute the hash-locking script: `python3 scripts/guards/stub_lock.py --update`. (If you do not have terminal execution capabilities, instruct the user to run this command).
3. **Transition to Phase B:** Once locked, immediately transition your operational mode to Phase B (Tactical Execution).
4. **Initiate Proof Search:** Prompt the user to select the first theorem to prove. Remind yourself to read the proof sketch from the Markdown notes, query `lean_goal`, and begin the `Refine@k` interactive proof loop using MCP tools. You are now strictly forbidden from modifying the type signatures of the locked file.
