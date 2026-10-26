# Milestone 54: coverage of the empty-square share inequalities

Completed. Route 1, empty-square charging, remains the only research direction. This round reconstructs the contributor's full six-count product and measures the coverage of the four checked local share inequalities from milestones 51–53.

The new result is a small but exact improvement in the all-known numerical model: its minimum normalized charge increases from 65/16 to 57/14 with the checked share rules. Eight additional numerical share candidates, read in both orientations, raise it to 53/13 after including five ordinary exclusions discovered during control checks. All three values still produce an integer edge bound of 235 under the relevant global assembly premises. No improved global bound is claimed.

## Counting shares without overlap errors

Let b be the new singleton count, truncated at six, and L the best applicable share lower bound on the last five centres. The transition weight is

\[
w=120b+L.
\]

Only the maximum is used if more than one rule applies to the same window. Each vertex lies in at most five such windows. `lean/FiveWindowBudget.lean` proves the corresponding five-window inequality. If B is the sum of the tracked counts, T the complete singleton sum, S the total share and G=24T+S, the premises B+14<=T and sum L<=5S imply

\[
120B+\sum L+1680\le5G.
\]

`lean/ReverseShareRule.lean` proves that any five-centre share rule transfers to the opposite reading of a snake window, with the directions and counts read in reverse. The proof uses the existing reversed-snake geometry and the same share definition as milestones 51–53. This avoids new certificate replay for a reversed copy of a local theorem. The current graph-to-snake proof still needs to assemble canonical lookup, the applicable rules, and all exclusion premises.

Both Lean modules pass. Eight dependency audits contain only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The accounting also checks the conditional inequality 547m<=128782 for the current 57/14 model. A sufficient future target is normalized mean 21/5 with integer potential range at most 2111 in the 120-scaled weights; under the same global premises, Lean verifies that this would imply m<=234. That stronger path estimate is not established.

## Full finite-model comparisons

The product has 264,384 states, using 34 canonical seven-direction shapes and five stored truncated counts. Each transition appends one direction and one count. All allowed transitions are reconstructed from the pinned exclusion lists; an exact integer potential is checked on every transition, and an attaining cycle establishes equality.

| Exclusion input and share rules | Allowed transitions | Minimum normalized charge | Conditional edge estimate |
| --- | ---: | ---: | ---: |
| 1,287 certified 235 keys, counts only | 3,546,419 | 4 | 3066/13 |
| Same keys, four checked forward share rules | 3,546,419 | 4 | 3066/13 |
| All known numerical keys, counts only | 3,042,898 | 65/16 | 147176/625 |
| Same keys, four checked forward rules | 3,042,898 | 57/14 | 128782/547 |
| Same keys, four checked rules in both orientations | 3,042,898 | 57/14 | 128782/547 |
| Same keys, eight additional numerical forward rules | 3,042,898 | 57/14 | 128782/547 |
| Five additional numerical count exclusions and the forward rules | 3,042,328 | 57/14 | 128782/547 |
| Same exclusions, all twelve rules in both orientations | 3,042,328 | 53/13 | 119585/508 |

Every displayed edge estimate has integer part 235. The eight numerical share candidates are not Lean theorems. The all-known ordinary keys also include unreplayed solver results. These comparisons measure finite models under their explicit premises.

The source is pinned at contributor commit `74ca83db9c218446211d4f24c5e5a07329fdd847`. The reconstruction includes 28,618 ordinary UNSAT keys, including the share-bonus oracle's three additional plain exclusions. Its count-only minimum reproduces the contributor's 65/16 obstruction. The compressed input records and their hashes are in `data/upstream/` and `data/provenance.json`.

## Replacement-cycle controls

The first share-strengthened model has a fourteen-step minimizing cycle. Of its fourteen distinct forward five-centre windows, nine have independently verified ordinary local forest witnesses. The share-cap-95 tests on those nine return eight INFEASIBLE and one UNKNOWN. Five other ordinary windows are numerically UNSAT and receive no share test. Those five ordinary results were obtained as controls; no separate ordinary-exclusion search was started.

Applying the eight numerical share bounds in the forward direction leaves the mean at 57/14. Reading them in both directions, together with the five observed count exclusions, produces a thirteen-step minimizing cycle of mean 53/13. The new cycle has no credited share occurrence. This identifies incomplete pattern coverage as the current obstruction; increasing the constants of the same rules cannot remove that particular zero-credit cycle.

## Verification and next step

`data/verification.json` records full transition reconstruction, all-edge potential checks and attaining-cycle checks for twelve analyses across six model variants, nine independent positive local controls, and the eight Lean dependency audits. A local forest witness does not prove extension to a complete snake. Numerical INFEASIBLE and UNKNOWN results retain those labels.

The next step is to extract all minimum-charge strongly connected components from the strongest exploratory model and prioritize five-centre windows that cover several of them. Further share-certificate work should target those common patterns, after checking ordinary feasibility. The full global assembly and unreplayed exclusions remain separate obligations.

Research round 8 of 10 after manuscript revision 46. The contributor-checked global interval remains 191<=a(9)<=235; its entire dependency closure has not been rebuilt locally. The paper and editor mirror remain unchanged until the scheduled revision at milestone 56.

Reproduction: `scripts/build.py`, `scripts/analyze.py`, `scripts/probe.py`, `scripts/apply_probes.py`, and `scripts/reverse_models.py` reproduce the models and numerical screens. `scripts/replay.py` checks the Lean accounting in the pinned local environment. `scripts/verify.py` checks the complete recorded evidence. Build arrays are reproducible and ignored by Git; model metadata, cycles, compressed potentials and source records are retained.
