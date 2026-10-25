# Milestone 50: a sharp triple inequality and targeted range optimisation

The integrated interval remains **191 <= a(9) <= 236**. Length is measured in edges. This is research round 4 of 5 after manuscript revision 46; both manuscript copies remain unchanged.

Verification status: **PASS**. All 429 Lean modules and 24 dependency audits passed, with only standard axioms. The independent audit also checks certificate provenance, explicit geometry, graph potentials and attaining cycles. The receipt is `data/verification.json`.

## Sharp six-step return inequality

Let a snake contain consecutive transition directions `(a,b,c,d,e,a)`, where the five labels are distinct. If `alpha_i` is the number of squares meeting the snake only at its vertex with index `i`, the new inequality is

\[
\alpha_{r+1}+\alpha_{r+4}+\alpha_{r+5}\ge13.
\]

There are no additional conditions on the intervening counts. A saved complete 143-edge snake attains the three counts `(3,5,5)` at indices 65, 68, 69, so 13 is the best constant for this local statement. This witness does not improve the 191-edge construction.

The proof excludes a sum at most 12 in the necessary radius-four model, replays an ordinary LRAT refutation, and transports the exclusion to arbitrary coordinate labels in an arbitrary snake. The core has 3,593 clauses and 1,354 active variables. Its replay contains 253,680 derived clauses and 10,807,572 hints. `TripleWitness.lean` checks the complete witness and sharpness. `TripleDemand.lean` converts the inequality into a common seven-centre excess demand without adding overlapping demands independently.

With counts clipped at six, an occurrence below total 13 either is impossible when all three counts are exact, or requires excess above six. The graph consequently loses 430,797 transitions and strengthens 148,609 retained demands. Its 3,424,976 remaining transitions still have exact normalized minimum mean 42/11. A cycle and an integer potential establish this finite-model statement. The universal graph-to-snake Lean bridge remains pending.

## Prioritising an actual improvement of the interval

The user's instruction shifted priority to changes that can tighten the range. The new screen therefore examines the entire recurrent minimum-mean family before selecting more proof replays.

1. All zero-slack cycle transitions were extracted using strongly connected components: 3,124 transitions, 1,385 states, and 381 canonical five-centre windows.
2. Testing all 381 upper-cap windows yielded 241 solver exclusions, 99 local forests, and 41 unresolved tests. Adding the exclusions removes 190,706 more transitions but leaves mean 42/11. The remaining minimum-mean family has only 20 transitions and seven five-centre windows.
3. Tests of hidden excess in the clipped-six positions yield 12 solver exclusions, seven local forests, and one unresolved test. Using the exclusions as common-window demands strengthens 4,254 retained transitions and raises the exploratory minimum to **23/6**. Its potential range is 728. The new minimum-mean family has 135 transitions, 92 states and 41 projected windows.
4. A cover of the 72,306 transitions violating the stronger potential reduces 253 candidate premises to 160 selected premises: 155 ordinary exclusions and five excess demands. Every retained transition was checked against the resulting integer potential. This cover is inclusion-minimal for the selected potential; minimum certificate count has not been proved.

The two exploratory graphs are in `screen/` and `excess-screen/`. Their potentials are exact certificates for those finite graphs, **conditional on accepting the new solver exclusions as graph rules**. The exclusions have not been replayed in Lean. No global improvement follows yet. The exact graph mean increases by 1/66, from 42/11 to 23/6.

## Quantitative targets

Retaining the empty-square term in the existing completed charge argument gives

\[
427m+22s_0\le101172.
\]

Thus 19 empty squares would suffice to exclude a 236-edge snake. Corresponding sufficient empty-square counts for upper bounds 234, 233, 232, 231 and 230 are 38, 58, 77, 97 and 116. Both initial direct tests of at most 18 empty squares returned UNKNOWN; they supply no exclusion.

For the present graph charge and boundary accounting, a hypothetical 236-edge snake has transition-charge budget 152,040. The improved potential supplies only 146,748, leaving 5,293 additional integer charge units needed for exclusion. Keeping potential range 728, the normalized mean would need to exceed 2728/687, approximately 3.970888. A convenient alternative sufficient target is mean four with potential range at most 1,847. `RangeTargets.lean` checks the arithmetic implications under their explicit premises; the universal graph and boundary premises remain separate obligations.

The next priority is to strengthen the 41-window replacement family, including exact bucket lower bounds, common excess and empty-square charges. Continue screening before replaying 160 premises whose present combined effect still gives only 236. A successful candidate must improve the mean or finite-path charge enough to cross the stated threshold, then receive proof replay and a complete geometric bridge.

## Reproduction and evidence

- `scripts/certify.py`, `replay.py`, `witness.py`: native certificate, Lean replay and explicit sharpness witness. `replay.py --resume` preserves source-matching successful builds.
- `scripts/graph.py`, `critical_family.py`, `critical_survey.py`: theorem-based graph and complete critical-family screen.
- `scripts/screen_graph.py`, `excess_survey.py`, `excess_graph.py`: exploratory exclusions and forced excess. These runs do not change the theorem-based graph.
- `scripts/pressure_cover.py`: selected proof workload and all-edge potential check.
- `scripts/controls.py`, `verify.py`: independent geometry checks, proof provenance, dependency audits, all-edge potentials and attaining cycles.
- `scripts/archive.py --unpack`: restore losslessly compressed native certificates before regeneration.

Independent controls check 107 local forests, all 131 complete bank snakes, and 948 oriented occurrences of the new return pattern. The minimum triple sum in that bank is 21; the separate 143-edge witness establishes sharpness at 13.

GitHub refresh found no later completed bound. Contributor branch `research/unconditional-241` remains at `b0ed28b7`, with 235 replay builds in progress; the 234 template on `claude/relaxed-keller-60ks7i` remains conditional at `8e9144df`. The completed 236 theorem remains pinned at `7cb52aad`. Repository and manuscript hashes are recorded in `data/`.
