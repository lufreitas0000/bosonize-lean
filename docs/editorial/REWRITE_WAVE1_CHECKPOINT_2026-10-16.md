# Chapter rewrite wave checkpoint — 2026-10-16

The user paused the first chapter rewrite wave on 2026-10-16. Three live Jules
sessions received a pause instruction to stop editing and wait for the user to
resume. No manuscript rewrite from this wave has been merged into `main`.

## Work completed

- Fifteen disjoint author tasks were prepared: CH01–11, CH19–21, and frontmatter.
  All fifteen have mechanically verified candidates. CH02 and frontmatter each
  needed one replacement session after their first session did not return usable
  source. The fifteen logical tasks used seventeen author sessions in total.
- The candidates passed the task whitelist, preservation checks, source inventory,
  and isolated compilation of the real book. The preservation baseline retains 583
  existing mathematical displays and theorem-like/proof blocks byte-for-byte.
- CH07's existing negative-charge arithmetic explanation was corrected in the
  candidate: the spurious `+ |N|` term was removed for `N < 0`. This is explicitly
  recorded as a coordinator copyedit; it is not attributed to Jules.
- The combined candidate is on `codex/editorial-rewrite-candidate` at
  `25f2955e4596a086137a9054b81a868444e3bbbf`. Its GitHub LaTeX workflow passed
  (run `38835553824`); its 196-page candidate PDF and source receipt were checked.
  This is candidate evidence, not the latest `main` release.
- Three separate Jules review sessions were opened for CH01–05, CH06–11, and
  CH19–21 plus frontmatter. They bring the wave total to twenty Jules sessions.

## Review status at pause

- **Foundations (CH01–05):** still in progress. The session was asked to pause.
- **Currents (CH06–11):** a mechanically valid report was returned, but coordinator
  inspection found generic line-one anchors, an inaccurate description of finite
  polynomial degree, and omitted known convention/BCH issues. A same-session
  correction request was sent; the session was asked to pause before continuing.
- **Interactions and frontmatter:** a mechanically valid report was returned.
  Coordinator inspection found CH21 tone/precision issues and report wording that
  misclassified a pre-existing bibliography gap. The report has not yet been
  revised to reflect these findings.
- **CH21 author:** its first candidate passed mechanical gates, but coordinator
  inspection found four phrases that do not match the requested modest tone or
  precise distinctions. A same-session correction request was sent; the author
  session was then asked to pause.

The three pause messages were sent through the existing Jules sessions. The
controller records for those tasks remain `waiting_jules`; the pause message does
not itself change their durable task state. Preserve the handles and resume by
collecting or continuing the same sessions. Do not dispatch replacement sessions
for this checkpoint.

## What remains before accepting any manuscript text

1. Resume the CH21 author and finish the requested narrow wording corrections.
2. Resume the foundations and currents reviews; inspect the revised reports against
   the source and candidate diff. Revise the interactions report so it records the
   CH21 findings and distinguishes pre-existing bibliography gaps from regressions.
3. Bind each independent review to the exact final candidate hashes, inspect the
   final disjoint changes, and integrate only after all source, preservation and
   combined-book checks pass.
4. Push the accepted `main` commit, verify its LaTeX CI, then check the published
   release PDF and its source receipt. The candidate PDF does not satisfy this gate.

This wave reviews explanatory prose and editorial consistency. It does not certify
all mathematics, reconcile global notation, move appendix material, promote Lean
work, or complete the separate CH12–18 exposition work. Those boundaries remain in
the wave brief and roadmap.

## Resume references

See [the wave brief](REWRITE_WAVE1.md), [current status](REWRITE_WAVE1_STATUS.json),
and the private operator checkpoint at
`/home/lucas/Projects/.agentctl/sprints/editorial-rewrite-wave1/RESUME.md`.
