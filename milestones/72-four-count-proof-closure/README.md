# Milestone 72: short-count proof closure and returning-direction restrictions

**Research round in progress, checkpoint 31 October 2026.** Ten certificate cases have completed their Lean chains and source/provenance audits. They remove 50,510 transitions from the proof-supported model and reduce the remaining additional premises for conditional 234 from 14,155 to 14,143. The global interval remains 191 <= a(9) <= 235. Six proposed certificate cases remain pending; the round is not complete.

## Completed mathematical results

Let a,b,c,d be distinct coordinate directions, and let the displayed word be five consecutive transitions of an arbitrary snake in Q9. Write alpha_1,...,alpha_4 for the singleton-square counts at its four internal vertices.

For the word (a,b,c,a,d), the following simultaneous bounds are impossible:

\[
(\alpha_1,\alpha_2,\alpha_3,\alpha_4)\le(2,4,5,5),
\]

and

\[
(\alpha_1,\alpha_2,\alpha_3,\alpha_4)\le(4,5,5,1).
\]

The additional componentwise bound $(\alpha_1,\alpha_2,\alpha_3,\alpha_4)\le(4,5,2,5)$ is also excluded. The componentwise bounds (2,5,5,4) and (5,5,2,3) are also excluded by the two newly completed proof chains. The bounds (3,5,3,5) and (4,5,3,2) have now also completed their audits. The inequalities are componentwise. These are upper-count exclusions, so they cover multiple exact-count premises. The first certificate required 13,918,327 LRAT hints and has now completed Lean replay.

For the word (a,b,c,d,a), the stronger returning-direction restriction is

\[
\alpha_1\le1\quad\Longrightarrow\quad\alpha_4\ge3.
\]

There is no hypothesis on the two intervening counts. Earlier completed certificates exclude the weaker upper-count tuples (1,5,5,1) and (1,21,21,1). They remain in the proof inventory as independently checked intermediate results; the final restriction subsumes them. No priority or novelty claim is made for these statements.

The completed cases are 7202, 7203, 7206, 7211, 7212, 7215, 7216, 7217, 7218 and 7219. `data/proof-audit.json` checks the current source hashes, successful compiled chains, original-to-core clause mapping, exported formula, and final theorem axioms. Thirty-two exclusion and corollary audits use only propext, Classical.choice and Quot.sound. The arbitrary-snake statements include coordinate normalization and the necessary geometric interpretation.

## Effect on both upper-bound tracks

The completed rules leave 4,947,008 transitions in the comparison model. Independent reconstruction checks each interval application, including the interpretation of symbol six as any count from six to 21. An all-edge integer potential and an attaining four-transition cycle establish exact minimum mean 480, with potential range 578. Thus these rules do not improve the current unconditional upper-bound estimate.

On the conditional track, the retained sufficient potential still gives

\[
136187m\le32003920,
\qquad m\le234.
\]

The updated fixed-potential selection contains 14,143 additional keys. Every selected key has a mandatory witness within the fixed candidate basis, and all 3,530,713 retained transition inequalities were checked independently. This least-cover claim fixes the graph, potential and candidate basis. The remaining count premises, complete arbitrary-snake history interpretation and complete Lean graph-potential replay are still outstanding. The completed local theorems do not by themselves establish a new global bound.

`data/proved-graph-verification.json`, `data/proved-old-verification.json` and `data/proved-selection-comparison.json` record these checks. Files without the `proved-` prefix also contain exploratory comparisons using pending exclusions; they must not be read as proof-supported models. Each model records exactly which cases it applies.

## Failed generalisations and controls

A saved acyclic local configuration for (a,b,c,a,d) has counts (5,3,6,2), summing to 16. Therefore the current local conditions do not imply a blanket four-count sum of at least 17. A second configuration has counts (4,9,10,1), showing that the middle-count hypotheses in the (4,5,5,1) exclusion cannot simply be removed from this local argument.

A local witness survives for (a,b,c,d,a) with the first count at most one and fourth count at most three. This provides a local control for the new returning-direction restriction; extension to a complete snake is not established. `scripts/controls.py` checks local cube adjacency, degrees, acyclicity, counts and the relevant bounds directly, and checks occurrences in all 131 saved complete bank snakes.

## Critical-family share investigation

The separate [critical-charge investigation](critical-charge/README.md) freezes the preceding six-case model and independently identifies all 18,865 minimum-charge cyclic transitions in six components. The share lower bound of 120 on a locally feasible five-centre window has now completed its Lean interpretation, refutation replay and arbitrary-snake normalization: 99 modules and 72 theorem audits. Admitting this candidate raises 1,280 weights in the current eight-case model but leaves the exact mean at 480. A separate comparison on the ten-case graph reduces the fixed-potential count basis from 14,143 to 14,142 when this share theorem is included. The global interpretation remains pending.

## Pending work

The exact tuple (3,4,4,4) for (a,b,c,a,d) remains unresolved here. The native certificate-producing solver timed out after 300 seconds. A separate sixty-second PySAT Cadical153 proof-output pilot also returned UNKNOWN after 990,115 conflicts. Neither result establishes an exclusion. The original numerical catalogue is retained as a separate source of conditional premises.

Generated certificates for several other cases are queued for Lean replay. The runner reuses successful modules only when the source hashes and dependencies match, combines the previous ordinary and fast proof records, and prioritizes shorter remaining certificates. A live process must be checked before any restart; saved record files alone do not prove that a job is running.

The next work is to complete those available proof chains, then reconsider the difficult exact cases using a different reduction or geometric argument. Repeating the same timed-out solver unchanged is not the current plan.

## Reproduction and manuscript status

The committed checkpoint includes completed proof sources in separate hash-checked archives and compressed native certificates. Local Git attributes preserve the exact audited Lean-source bytes and raw verifier logs; staged source hashes were checked against the proof audit. Run `scripts/archive_lean.py --restore` to restore or match the completed source files before a fresh replay. Run `scripts/archive.py --unpack` before auditing archived native files. `scripts/audit_proofs.py` explicitly separates completed and pending cases. Use `scripts/graph.py --proved-only`, `scripts/analyze.py --proved-only`, `scripts/verify_graph.py --proved-only`, `scripts/select_keys.py --old --proved-only`, and `scripts/verify_selection.py` for the proof-supported comparison and conditional selection.

Pending generated proof sources and intermediate build objects remain local until their checks complete. `scripts/certify.py --case NUMBER` regenerates a selected certificate. The original short probe can be UNKNOWN: a fresh native refutation, independent DRAT check, LRAT export and Lean replay are still required before admitting that case. `scripts/replay.py --cases LIST --resume --include-record fast` reuses both recorded proof batches; omit the resume flags for a first build.

The manuscript remains at revision 66. Round 72 is the sixth research round after that revision, still in progress. The next full manuscript rewrite remains scheduled for milestone 76. Both paper sources are unchanged.
