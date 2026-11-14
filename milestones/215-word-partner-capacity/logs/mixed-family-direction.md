# Mixed distinct-word families: frozen case22 assessment

Mixed families give valid additional Hall constraints. However, the thirteen saved regions examined here show no additional propagation after the existing four-family Hall rules and binary relations reach a fixed point. This is a possible extension for later states, with no demonstrated benefit on this snapshot.

## Inputs and scope

The analysis reads only the immutable transferred round214 state, the original model and the family catalogue under `215-word-partner-capacity/data/case-22`. The state records 240 committed jobs, 1,801,017 nodes and thirteen open regions. The changing round215 frontier was not read.

SHA-256 pins:

- `model.json`: `1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b`
- `transfer214-state.json`: `eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027`
- `support-constraints.json`: `0362c97affd2b4b19405f2a05747327a703b55459b6f1cb3d7bc455c72bce040`
- `scripts/analyze_mixed_families.py`: `e0aeac82b490dfe7b54ca9afd95cb48e51e7ed3c08331741cd2af337d56290d8`
- `data/mixed-family-analysis.json`: `4c2f6c6fc0926963ebfcbba6aaad9a062b5b07031bc453fa4c60dab57403d7d8`

The deterministic computation uses bipartite augmenting matchings, tight reachable subsets, and binary arc filtering. It has no branching search, solver, compiler or software tests. Its fixed-point comparison is limited to the four family constraints and the saved binary relations; partner-budget rules and saved higher-order nogoods are omitted. It is neither a Lean certificate nor a claim about the current frontier.

## Geometry and maximal families

Within one interval-ID parity, equal words in different intervals require singleton intervals at opposite retained-square corners. An interval with multiple retained vertices therefore conflicts with every other interval of that parity. Singleton intervals at the same or adjacent corners also conflict.

Consequently, every maximal family of pairwise unequal words consists of all multi-visit intervals, one complete singleton family from corners 0 and 3, and one from corners 1 and 2. All four corner families are nonempty in case22, so there are exactly four maximal families per parity. Checking the diagonal of every saved binary relation on the parity alphabet agrees with this geometry for every pair: 660 even edges and 631 odd edges, with no mismatch. This comparison uses fixed relation diagonals; dynamically removing possible equality words could enlarge the conflict graph and was not examined.

| Parity | Multi-visit intervals | Singleton counts at corners 0,1,2,3 | Maximal family sizes for corner choices (0,1), (0,2), (3,1), (3,2) |
|---|---:|---|---|
| Even | 12 | 5, 4, 9, 9 | 21, 26, 25, 30 |
| Odd | 9 | 8, 9, 6, 7 | 26, 23, 25, 22 |

The existing chosen families have sizes 30 and 26. Their outside families have sizes 9 and 13 and omit all multi-visit intervals. Those outside families lie in maximal families of sizes 21 and 22. The other two corner orientations in each parity give two further maximal families. Thus eight maximal families cover the four currently used families and all smaller geometric cliques.

## What the snapshot actually shows

A single pass on the unmodified domains finds 35 candidate deletions from the eight maximal families beyond those found in a single four-family pass. They occur in regions 20, 18, 17, 16 and 246, with respective counts 5, 6, 12, 6 and 6. Neither first pass finds a deficient family.

Repeating the existing four-family Hall rules and the original binary arc rules changes this assessment. Twelve regions reach a fixed point in two or three rounds. Every candidate mixed-family deletion there has already been removed. Scanning all eight maximal families on those fixed points yields zero additional deletions and no deficiency. Region 246 instead becomes Hall-deficient under the existing rules after two rounds. The computation therefore supplies no instance where a mixed-family deduction survives the existing-rule comparison. The region246 observation is confined to this saved-state computation and is not a published native exclusion.

The first-pass totals in the JSON summary must be read together with each region's `four_family_binary_closure` record. Reporting only the 35 candidates would overstate the result.

## Logical strength and a bounded next step

Mixed Hall constraints can be stronger than separate chosen/outside all-different propagation plus binary inequality arc consistency in an abstract domain state. Take one multi-visit interval and two outside singleton intervals at adjacent corners, and give all three the same two-word domain. The three are pairwise unequal. The separate families see one variable and two variables; binary inequality arcs retain both words. Their mixed three-variable family has a two-word union and is impossible. This example proves a distinction between the propagation rules. It does not show that this domain pattern is reachable under all constraints of case22, including its additional Hamming restrictions and partner-budget rules.

A small subsequent extension could use the eight maximal families and reuse the same domain-union capacity argument. No new geometric principle is required: `ConcreteSupport213.required_words_ne` already treats within-chosen, within-outside, and outside-to-chosen nonpartner pairs. A literal membership certificate covering each mixed family's unordered pairs, with reversed inequalities where needed, should supply its distinct-word premise. That membership certificate and the extended Lean composition remain unwritten and unchecked. The current round215 family-selection theorem names only the four original lists.

The proposed snapshot improvement is refuted by the existing-rule comparison. The 35 first-pass candidates do not justify adding mixed-family propagation. Its general search benefit, overhead and interaction with stronger partner-support rules remain unresolved. No new snake, global bound, or completeness result follows.

## Word-restricted spare capacity

Suppose the duplicate-free chosen subset \(C_U\) and outside subset \(J\) both have domains contained in a word pool \(U\). Let \(N_U(J)\subseteq C_U\) contain every chosen variable that could share with a member of \(J\). Distinct chosen values use \(|C_U|\) words of \(U\); at most \(|U|-|C_U|\) outside values can avoid them. Distinct outside values sharing with \(C_U\) use distinct members of \(N_U(J)\). Therefore

\[
|J|\leq |N_U(J)|+|U|-|C_U|.
\]

If \(|C_U|>|U|\), ordinary chosen-family Hall already gives a contradiction. Otherwise this inequality is exactly

\[
|C_U\setminus N_U(J)|+|J|\leq |U|.
\]

With complete antipodal partner lists, and with \(N_U(J)\) defined by those lists without domain-intersection pruning, the family \((C_U\setminus N_U(J))\cup J\) is a geometric clique. Its domains lie in \(U\), so the localized spare inequality is precisely its mixed-family Hall condition. It introduces no further necessary condition beyond Hall on all geometric cliques, hence beyond all subsets of the eight maximal families. Conversely, a mixed clique with chosen part \(A\) and outside part \(J\) is recovered by setting \(C_U=A\): its partner neighbourhood within \(A\) is empty.

If \(N_U(J)\) additionally omits allowed antipodal partners whose current domains are disjoint, the same rearrangement is Hall on a family with additional domain-dependent inequalities. It need not be contained in one of the eight fixed geometric maximal families. Equivalence with those eight families after propagation is not established here. This distinction must be settled before describing localized spare capacity as a stronger direction. No additional computation or proof implementation was performed for this observation.
