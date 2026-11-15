# Round 223 bounded document review

Review date: 15 November 2026. Final finding: no unresolved substantive issue in the reviewed manuscript changes. One supporting-note/table scope discrepancy was identified and corrected by the parent agent during review. The saved native results and their executable sources were preserved.

## Scope actually read

- Complete diffs from `data/snake9_research.tex.before.txt` and `data/snake9_frontier_explanation.tex.before.txt` to the current manuscript mirrors; editor originals are byte-identical to those mirrors.
- Current main source lines 1–95, 7700–7992, including the complete abstract, new subsection `sec:coupled223` at lines 7715–7814, and the entire current verification section at lines 7816–7987. The main source contains 11445 lines.
- Every current short-frontier line, 1–469.
- Every line of the final `MATHEMATICAL_NOTE.md`, 1–61.
- Complete `FourCrossings223.lean`, lines 1–137, and `Endpoint223.lean`, lines 1–59; both accepted audit and execution receipts.
- Complete semantic difference between `coupled_search.py` (128 lines) and `endpoint_search.py` (133 lines), the complete endpoint preparation script (21 lines), endpoint scope/case records, search summary, and the relevant native result/execution fields. The full base model had already received the separate review in `logs/model-review.md`.

This is the requested revision review. It does not repeat the complete manuscript review performed in round 220; the next complete review remains round 230. No manuscript or executable source was edited by this reviewer. No solver, compiler or software tests were run. Reading, hashing and comparing saved artifacts did not replay any native search or Lean proof.

## Final document identity and preservation

Editor originals are under `D:/Codex/2026-10-13/new-chat/outputs/`; matching mirrors are under `E:/Snake-in-a-box/paper/`.

| Document | Final SHA256, identical for editor and mirror |
|---|---|
| `snake9_research.tex` | `47a5328d5120bb718b94034653f56fa704fba6796f43bd55a796630bb0132e10` |
| `snake9_frontier_explanation.tex` | `1c60c266904a1d06c9a83eda374679cf1a2020e33dd3a29d18f3bbc1511ba2db` |
| `MATHEMATICAL_NOTE.md` | `5074ceb8ba94659a133cb83472668f3895136678ec2e9d0267fcb2323f94f48a` |

The main before-source SHA256 is `0ec5b0ec20672646bec75602ba7530c121f4755f8bd7423c73de727a06c6ba89`; the frontier before-source SHA256 is `72aa8cea5cc715571e175b11527001fd2c1dc868f0d3ff6453f94ef61a8089c7`.

Both author declarations are unchanged and retain Iori Hironaka, Tommy Ma and Steven Zhan. The complete balanced-brace main `hypersetup` block is unchanged, including its three-author PDF metadata. The frontier has no `hypersetup` block in either version; its hyperlink package setting remains unchanged.

All 351 earlier main labels remain, in their previous order. The only added labels are `sec:coupled223` and `prop:five-join223`, bringing the count to 353, without duplicates. All 120 earlier main bibliography keys remain in order; only `research223` is added. The frontier retains all five earlier bibliography keys and adds the same reference. It contains no labels in either version.

## Mathematical and evidence assessment

1. The five-component proposition states sufficient compatibility hypotheses correctly. Consecutive components share only their prescribed projected endpoint; all four nonconsecutive same-face pairs are disjoint and nonadjacent; the two nonconsecutive opposite-face pairs are projection-disjoint. These conditions exclude repetitions and every unintended edge. The length is the sum of five component lengths plus four crossings. The Lean constructor uses these hypotheses through the existing append/layer machinery. Neither manuscript treats the constructor as a new witness or a solver contradiction certificate.

2. The selected seed data agree with the source review and native records: bank entry 123, normalized crossing bit 8, component edge lengths 46, 83, 32, 13, 13, face occupancies 94 and 98, endpoints 0 and 88. The target has 193 vertices. With endpoint 0 and four bit-8 crossings, its other endpoint must be an even vertex in the lower face. The 97-even/96-odd cardinalities are necessary. The degree equation is correctly described as conditional on selection. Both-face omissions and the total omission budget are expressly restricted search conditions. They do not themselves force a port change.

3. The native results match `search-summary.json`: four omissions give `INFEASIBLE` in 3.204 solver-loop seconds; eight and twelve give `UNKNOWN` in 120.063 and 150.031 seconds. All three execution receipts have exit code zero and `ACCEPTED_NATIVE_RESULT`. Their result and execution hashes agree with the summary. Their serialized initial model hashes agree with the corresponding result records. All cycle-cut lists are empty and all witnesses are null. The manuscript's “at least five omissions and six additions” consequence is confined to the specified seed alignment, endpoint, crossing coordinate and both-face changes. It is reported as a native exclusion with no Lean contradiction certificate. Unknown results are correctly left unresolved.

4. Endpoint specialization adds a required endpoint argument, checks that it is an even lower-face neighbour of 88 absent from the seed, fixes its endpoint flag to one, and retains vertex 88. It retains all other mathematical constraints. For the actual argument 80, the endpoint pair is 0 and 80, so retained 88 is internal. Since 80 is adjacent to both 88 and 208, its selected degree one forces omission of 208. The seed records place 208 at index 163 and identify it as an old crossing port. Thus this variant forces a port change. The endpoint-80 result is `UNKNOWN`, with 75.000 saved solver-loop seconds, exit code zero, no witness and no dynamic cycle cuts. Its initial model hash and executable-source pin agree. The manuscripts correctly claim neither a construction nor an exclusion from this run.

5. Both accepted Lean receipts report `PASS`, exit code zero. `FourCrossings223` reports one public constructor result in 5.141 seconds, using `propext`, `Classical.choice` and `Quot.sound`. `Endpoint223` reports two endpoint results in 2.140 seconds, using `propext` and `Quot.sound`. Saved source, compiler-log and object hashes were independently compared with both receipts and agree. This confirms receipt identity; it does not constitute a new compilation or independent dependency rebuild. The coordinate calculations and concrete solver infeasibility remain outside these generic Lean results.

6. The maintained interval remains $191\le a(9)\le233$, with the contributor theorem's independent full rebuild pending. The inherited fixed-parent ceiling is still expressly limited to the saved parent and its cube-isometry class, with no compatible 92-edge witness or attainment claim. No changed text upgrades that ceiling to a global upper bound. The final contributor observation pins revision `4b6b73907af9d76d7a8f3ca592a13dc89c8ad21d` and records work in progress; the note does not assert a completed 231 or 232 bound. This review read that saved observation and did not independently fetch or rebuild the contributor branch.

## Issue disposition

The initial supporting note described all eight neighbours of 88 as new endpoints, although 89 is already the seed predecessor at index 190 and `endpoint_search.py` excludes endpoints already in the seed. The corrected table now marks `already_in_seed` and `eligible_new_endpoint`; the note and generator explicitly distinguish eight lower-face neighbours from seven eligible new endpoints. The blocker row for 89 is retained as an ineligible geometric entry. This resolves the scope discrepancy. The endpoint-80 run and both manuscripts were unaffected.

The immutable endpoint native result still contains the inherited phrase “other endpoint free”, followed by its explicit specialization. Its actual command, equality and separate `endpoint-scope.json` fix endpoint 80 unambiguously. The note transparently records this metadata limitation; it is not a model ambiguity or an outstanding manuscript correction.

No further local or structural change is required by this bounded review. No PDF rendering or publication result was reviewed here.

## Supporting artifact hashes

| Artifact | SHA256 |
|---|---|
| `scripts/coupled_search.py` | `ad4328aeca4b8b61ad02dcae0a078075eb5c84a3611ddf193c84a3aa63ecf068` |
| `scripts/endpoint_search.py` | `f594a99bb767aad1a8823f6e845c125fcaa82fcdaefab0b24610c7c3c97f9e2b` |
| corrected `scripts/prepare_endpoints.py` | `5ae99337b7e9722d5b7e59336e2312a9b3a3554f538ddc1fb8a4c07f93834822` |
| corrected `data/endpoint-cases.json` | `62e5f7c25a0efe88660032b2caee7ec0d01b07f2e58f603a5af72b5f98b7be46` |
| `data/endpoint-scope.json` | `eef9ae64058c924c5fe94940bb4fbbad1e61f061e6b62538f8c78440f29d2c0f` |
| `data/search-summary.json` | `8f8e3791940cd0f914f7b3a201f284e66d3178a26ab30c075c23fa84c26e5edf` |
| `data/FourCrossings223-audit.json` | `2d097d2c788ee5cc678dcb753fb676a602b4c6a5452778c76f6e861da531f553` |
| `data/Endpoint223-audit.json` | `efd33141be46ced29f03f71d31971f960b700582f266735f8bcdbc6663b4d6d5` |
| `lean/FourCrossings223.lean` | `59224745997608079c9ac19f86ae94a3d791400358af0370e41ead8257a4a605` |
| `lean/Endpoint223.lean` | `edf34bb58b95eaa7a537100bd5945bbfdc1b36fc43f220edf5726abf5054ebab` |
| `data/github-final.json` | `353f36dba871e3f2cfc395af376cc19cee07ccb32b4e2fb2289b870a671fe5c4` |
