# Round 200 manuscript review: current limitations and historical material

Reviewed `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`, all lines 3035–6302 inclusive. Line references below refer to that source as read during this review. The assigned range was read completely, including every row of both exclusion tables. No manuscript edits, proof builds, tests, searches for new witnesses, or memory changes were performed.

## Findings requiring a narrow correction

### Finite-walk qualification in the direction-aware automaton paragraph

- Location: `sec:window-aggregate`, paragraph “A direction-aware automaton,” line 5903.
- The sentence says that admitting unexamined windows makes the minimum cycle mean “a valid lower bound on the average internal count.” For a finite snake, a minimum cycle mean alone does not imply that unqualified average bound. An open walk can have a lower average because of its initial and final potential values. The subsequent proposition correctly includes those boundary terms, so this does not invalidate its stated numerical deduction.
- Suggested replacement for the relevant clause: “Windows not yet examined are admitted. The minimum cycle mean controls the long-run average count; finite snakes require the boundary terms in the potential summation below.”
- Classification: mathematical scope clarification in explanatory prose; no change to the proposition or bound.

## Minor clarification, not a mathematical error

### Why a seven-symbol count model is checked on eight-valued tuples

- Location: `sec:window-aggregate`, lines 5877–5884.
- The proof defines 49 pairs of positive clamped counts and then mentions checks over all `8^3` and `8^4` clamped tuples. The underlying files `work/spectral/stronger/WindowPotential242.lean` and `WindowPotential241.lean` explicitly enumerate values 0 through 7. Their step predicates include positivity guards, so tuples containing zero impose no step inequality. The extra value is intentional; there is no coverage gap.
- Optional concise clarification: replace “all $8^3$ clamped triples” by “all $8^3$ triples over $\{0,\ldots,7\}$, with positivity imposed,” and make the analogous change for quadruples. This is lower priority than the finite-walk qualification.

## Status and consistency assessment

No substantive contradiction was found in the assigned text concerning the following distinctions:

- Lines 3981–3982 and 4045–4052 retain the project interval $191\le a(9)\le235$ with an archived contributor audit and an explicitly pending independent rebuild. This agrees with the current handoff record; the review does not upgrade that evidence.
- The six-step 233 comparison remains conditional in `sec:slack233` (3898–3967). Its source/compilation inspection is distinguished from an independent rebuild, and its local certificates and actual-snake integration remain open.
- The retained-graph 234 comparisons distinguish exact numerical edge scans, Lean arithmetic deductions, local Boolean refutations, and the unfinished universal interpretation. The present sufficient pending profile $(15,14,14,14)$ is clearly separated from earlier stronger profiles in lines 3971–3978 and 4061–4070.
- The boundary-21 optimality statements are explicitly scoped to their earlier boundary constants. The later boundary-24 comparisons therefore do not contradict them. The uniform floor-fourteen loss-two result and the critical floor-fifteen loss-zero profile also have distinct hypotheses.
- Historical “completed floors” labels are explained as fixed archived weight profiles at lines 4189–4193. Later share results do not silently change the means of those archived graphs.
- The round-185, 186, and 187 partial interpretation records have explicit chronological cutoffs (3866–3896). They should not be rewritten as fresh completion claims. The current status record reports no subsequent independent completion that would require an upgrade here.
- The 236, 238, 241, 245, 247, 248, 251, 254, and 255 bounds are introduced as earlier or intermediate results, so their coexistence with the qualified 235 record is consistent.
- The 196 conjecture is explicitly motivated by extrapolation only. The alternative prediction 195 and the statement that the recurrence supplies the same evidence prevent it from being presented as a proved bound or independent corroboration.

No additional substantive ordering change is recommended. The large historical sections are already marked as appendices and retain their original hypotheses. Moving the partial replay chronology is an editorial preference, not a correction needed for mathematical validity.

## Complete reading coverage

| Lines | Section labels and material read |
|---|---|
| 3035–3136 | `sec:proved-count-refinements`; the 012310 five-count sum, `sec:seven-cycle-exclusion`, and `sec:five-count-exclusion` |
| 3137–3412 | `sec:current-limitations`; `sec:share18-unaffected-cycle`, `sec:joint-share-floors`, `sec:range156`; all cycle/range inequalities and profile qualifications |
| 3413–3570 | `sec:retained-loss-comparison`, `sec:boundary-retuning`; zero-loss examples and least-floor comparison |
| 3571–3897 | `sec:floor14-loss`; both loss thresholds, exceptional-corner geometry, rational-share rounding, extension reduction, native certificates, one-floor-fifteen profile, and partial interpretation chronology |
| 3898–3968 | `sec:slack233`; four- and five-unit allowances, conditional arithmetic witnesses, and remaining table coverage |
| 3969–4043 | `sec:closure`; current and earlier obligations, reference union, full-edge certificates, and contributor comparison |
| 4044–4180 | `sec:verification`; archived 235, local proof status, completed 012032 floors, partial 012301/012034 replays, and conjecture qualification |
| 4181–4401 | `app:historical-comparisons`; seven-centre model, `sec:joint-optimality`, `sec:short-walk`, and `sec:unsaturated-obstruction` |
| 4402–4935 | `sec:sum-refinements`; all ten sum-rule rows, successive replacements, odd-length refinement, occurrence-credit obstructions, five-count deletion, `sec:share-floor-range`, and integer thresholds |
| 4936–5000 | `app:historical-verification-records`; milestone-143 through milestone-146 certificate cutoffs and initial-database connection |
| 5001–5089 | `app:earlier-long-models`; reweighting, complete and restricted models, history ambiguity, and tight-edge extraction |
| 5090–5154 | `app:earlier-five-model` / `sec:current-charge`; budget, comparison table, zero-credit cycle, and conditional future target |
| 5155–5209 | `app:bound236`; 732-row exclusion claim, potential, internal-count summation, and upper-bound deduction |
| 5210–5235 | `app:pair-caps`; complete printed pair-cap table and its stated scope |
| 5236–5913 | `app:geometry`; Huang argument, square counterexample and identity, adjacent-count exclusions, aggregate refinements, full printed three-count classification outline, endpoint demands, radius-three forest, and finite-window potentials |
| 5914–5936 | `app:counters`; threshold clauses and both directions of their counting interpretation |
| 5937–6014 | `app:bound238`; radius-three exclusions, potential, boundary summation, and deduction |
| 6015–6206 | `app:exclusion-catalogue`; introduction and all 175 numbered direction/count rows |
| 6207–6250 | `app:research-targets`; charge targets, six-four conjecture, frequency consequence, and singleton-density limitation |
| 6251–6302 | `sec:hypothesis`; known-term table, model, 196 conjecture, recurrence, 195 alternative, and limitation |

## Evidence consulted and limits

Read the current `handoff/CURRENT_STATUS.md`, `milestones/199-parent-diversity/MATHEMATICAL_NOTE.md`, and `milestones/199-parent-diversity/data/completion.json`. These records confirm no new Q9 witness or global bound, pending independent rebuilding of 235, and conditional status of 233/234. The recent symmetry census is outside this assigned manuscript range; its numerical exclusions were not re-audited here.

Read `work/spectral/stronger/WindowPotential242.lean` and `WindowPotential241.lean` to resolve the seven-symbol/eight-valued enumeration issue. This was source inspection only. Their old module comments describe historical conditional status and were not used to override the manuscript's later completion records.

The review examined the written arguments, indexing, profile changes, displayed arithmetic, and claim-status boundaries. It did not independently replay the large certificates, reconstruct millions of graph edges, rebuild the archived dependency chains, check every catalogue row against its certificate, or render the document. The printed three-count classification expressly omits branches; those omitted branches were not reconstructed. No theorem is newly certified by this report.
