# Round 230 final document review

Result: no blocking mathematical or status inconsistency found in the inspected final passages. The documents consistently state complete native exclusion of the specified fixed-seed two-block family through width 46, while retaining the limits of the three Lean components and the unchanged global research interval.

## Exact coverage of this review

Read the following complete line ranges from the final source:

- `paper/snake9_research.tex`: 1–145, 8245–8395, and 8615–8650. These include the abstract, principal result and reading guide, the preceding round-229 status, all of `sec:facevisits230`, the new proposition and proof, and the verification paragraph.
- `paper/snake9_frontier_explanation.tex`: 1–84 and 447–564. These include its opening status and the entire new construction, face-visit, and remaining-questions discussion.
- All of `milestones/230-two-crossing-frontier/MATHEMATICAL_NOTE.md`; the corrected opening of `logs/face-visits-proof.md`, whose remaining proof was read in the preceding model review.
- All of `scripts/close_free.py`, plus the saved aggregate data and its six pinned dependencies.

This is a bounded review of the requested final passages, not a new full-manuscript review. It does not compile or render either document, rerun Lean, rebuild the contributor's upper-bound chain, or replay native searches. The earlier complete source reviews retain their own scope.

## Claims and dependencies

The proposition correctly separates zero crossings from the run-count argument. For positive crossing count the two endpoint visits are distinct, every interior visit contains at least three vertices, and the incidence identity gives both face inequalities. Adding them uses the total vertex count \(u+l=m+1\) and yields \(3c\le m+2\). Consequently the stated maximum of sixteen crossings for a 46-edge replacement is correct. The result concerns a chosen coordinate in any cube dimension and carries no unsupported novelty claim.

The text correctly identifies the three accepted Lean components and leaves extraction of maximal visits and their incidence identities from a whole path as a written argument. It explicitly separates those components from finite input preparation, cover assembly, and solver contradictions. The corrected proof-note opening now gives the accepted source hash and axiom-report count; its former uncompiled status is no longer presented as current.

The restriction to at least eight total crossings includes all needed premises: both full endpoints lie in the same face, each residual context retains a positive number of crossings, and two, four, and six have completed exclusions in the same contexts. The face-visit queries impose no boundary-change restriction. Earlier four-crossing boundary dependencies remain confined to their historical cover. The six-crossing discussion explicitly avoids applying its exclusions to the nine initially unresolved cases before their separate unrestricted exclusion.

The arithmetic of the final coverage is consistent throughout:

\[
106+198+11=315.
\]

The exact-two stage has fifteen completed reduced queries. The final stage has eleven completed first-solve exclusions. No historical timeout is promoted directly to an exclusion. The former eleven open contexts are clearly dated to the round-229 cutoff and followed by their present closure.

The scope is stated as the normalized bank123 seed, appended vertex 24, two separated replacements preserving their respective lengths, retained anchors and outside positions, and replacement lengths at most 46. Padding is used only to move a smaller replacement into a containing maximal context while preserving the complete candidate. The documents do not extend this result to other seeds, endpoints, unrestricted reconnections, or a global upper bound.

The abstract and reading guide retain the global interval and the independent-rebuild limitation of the archived contributor theorem. They state that no longer snake or matching global upper bound was obtained. The suggested endpoint/seed survey, wider replacements, and length changes are future directions; no unperformed survey or improvement is claimed. The mathematical note explicitly records the requested pause after publication.

## Aggregate and source integrity

Independently reconstructed every row of `coverage-free46.json` from the prior table and the eleven audited terminal visit results. All 315 rows match exactly; the prior 304 rows are preserved. The eleven new rows have current status `NATIVE_EXCLUDED`, batch `visits46`, and the exact saved result. Aggregate counts distinguish 198 prior and eleven new native exclusions. Historical `last_status: UNKNOWN` fields are retained history, rather than current unresolved status. The final `unresolved` list is empty.

An initial reviewer comparison expected separate prior/new labels in each row. Inspection of `close_free.py` showed those distinctions reside in aggregate counts and batch fields. Corrected exact reconstruction passed; no evidence or producer source was changed.

The six aggregate dependency hashes match. The model archive named in the note exists; archive-content verification was not repeated here. Each editor original is byte-identical to its `E:/Snake-in-a-box/paper` mirror. Author commands and complete `hypersetup` blocks match the round's before snapshots in both documents. The three new main-paper labels are unique, and the `research230` bibliography entry exists exactly once in each document.

## Final source pins

| File | SHA-256 |
|---|---|
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex` and identical paper mirror | `5531889a5f4cff02d375722b07126d1d3312245d5040570a2424761f98d4169a` |
| `D:/Codex/2026-10-13/new-chat/outputs/snake9_frontier_explanation.tex` and identical paper mirror | `d9fd4450f8cf92706d0d20d4a5b298451ecc4663f95a6220d4c464991f25dc26` |
| `MATHEMATICAL_NOTE.md` | `4f653f22ff32ea566b76a74484d67579cb5f34a874933579f16b9aa70cfd8986` |
| `logs/face-visits-proof.md` | `7cb5855e3462aef8bae21771833a3c91ef62e465ade16b1073ce4440bbd245be` |
| `data/coverage-free46.json` | `526717ff410831ab313d807df0c619640318ffc105b43c5447213fbe08044295` |
| `scripts/close_free.py` | `40c27ddaab2482a3458680f317f4cc4eacb33efbb74368747bab8200a3f0498c` |

The main source has 12,138 lines and 760,820 bytes; the short explanation has 650 lines and 34,345 bytes. This review changes only its owned review files. Manuscript compilation and final publication remain the parent's separate verification steps.
