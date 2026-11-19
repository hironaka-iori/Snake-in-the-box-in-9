# Round 248. Extremal partners of five intact 96-edge arms

**Result.** Fix any one of the five eight-dimensional 96-edge parent shapes from the 25 published one-crossing examples. The longest nine-dimensional snake formed by joining that parent to an arbitrary path in the opposite face has **191 edges**. At only one endpoint can the parent accept a 94-edge partner. For the fixed labelled parent there are exactly five such partners at that endpoint. These are precisely the five previously recorded for it. [Complete coverage and witness audit](aggregate.json) · [Ordered extremal partners](attainers.json)

The five shapes are labelled 0, 3, 4, 5 and 8 by the first saved example in each class. Endpoint 0 is the joining endpoint of the stored example. Labels and translations affect the count of placed paths, so the statement fixes the parent before counting partners. The global optimum is open. [Parent definitions and data](../246-eight-dimensional-parents/arm-structure.json)

## Why the 95-edge search is exhaustive

Translate a joining endpoint of the parent to zero. A partner in the other face starts at zero and may use any other vertex outside the parent. A second projected intersection would give a chord between the faces. Conversely, a single shared endpoint suffices when both arms are induced paths. A 95-edge partner would give $96+1+95=192$ edges. Any longer partner contains a rooted 95-edge prefix. [Dimension-cut construction](../246-eight-dimensional-parents/README.md)

There are seven possible first steps from each of ten labelled endpoints. Four root exclusions from Round 247 cover 28 first steps. That round also certified 26 first steps individually. The 16 remaining queries all excluded a partner of 95 edges. The native survey and the independent proof checker agreed on every new exclusion. The verifier regenerated the formula and replayed the refutation to the empty clause. [Previous coverage](../247-relative-middle-placements/partner-children-summary.json) · [Native survey](survey.json) · [Sixteen certificates and replay receipts](certificates.json)

## Which partners attain the upper bound?

A 94-edge partner has 95 vertices, 48 even and 47 odd in the rooted labelling. Its second endpoint must be even. With the opposite endpoint of each parent as root, this query was refuted in all five cases. At the published joining endpoint there are five known partners per parent. All 25 transports have explicit isometries and complete ordered paths. [Endpoint evidence](endpoint94.json)

To establish completeness, block each accepted set of 95 vertices. Under the exact cardinality constraint each such clause excludes only that vertex set. An induced path with specified starting vertex has a unique traversal. A disconnected degree solution contains a cycle, and all vertices of an induced cycle cannot lie in an induced path. Each of the five parent queries produced two cycle cuts and then a checked refutation. Independent classification up to ambient cube isometry and path reversal compares every surviving joined path with the published bank. [Extremal census](attainers.json) · [Independent coverage audit](aggregate.json) · [Published record and snakepit methods](https://arxiv.org/abs/2607.15270)

## Symmetry and limits of local bounds

Across the five parents, the optimal partners represent five shapes up to cube isometry and reversal. Each of the five parent shapes pairs with each of the five partner shapes. The resulting 25 joined paths remain distinct under nine-dimensional cube isometries and path reversal. [Class-by-class census and bank indices](aggregate.json)

After the first step $0\to s$, remove the consumed zero vertex, neighbours of zero other than $s$, and the forbidden parent vertices. Keep the component of $s$. A rooted 95-edge partner exists precisely when the resulting graph has a 94-edge path starting at $s$ and meeting its inherited constraints. A permutation of coordinates after translating $s$ to zero transfers an exclusion if it maps the whole candidate domain into an already excluded domain. The 70 first-step domains belonged to 70 different rooted cube-isometry classes. None of the 16 open domains was contained in one of the 54 previously certified domains under such a map. [Domains, permutations and coverage](transfer.json)

An independent calculation used allowed selections in four-dimensional faces and linear degree, parity and connectivity constraints. Its integer-checked bounds for the 16 cases ranged from 96.397901 to 98.809567 selected vertices. The target requires 96. These particular bounds leave all 16 cases open, which explains the role of the proof certificates above. [Capacity bounds and integer coefficients](capacity.json)

Propagating the locally allowed even and odd counts across every coordinate split still admits 48 vertices of each parity in all 16 cases. For parent 0, endpoint 0 and first vertex 1, adding explicit face constraints to the full path formula provided a second, independently replayed exclusion. [Face counts](face-capacities.json) · [Second proof for the selected case](conditioned-replay.json)

## What changes when the joining endpoint is reversed?

| Eight-dimensional parent | Longest partner at the published endpoint (edges) | Longest partner at the opposite endpoint (edges) |
|---|---:|---:|
| 96 edges, shape 0 | 94 | 90 |
| 96 edges, shape 3 | 94 | 91 |
| 96 edges, shape 4 | 94 | 91 |
| 96 edges, shape 5 | 94 | 75–90 |
| 96 edges, shape 8 | 94 | 89 |

Each exact value has an ordered witness and a checked exclusion at the next length. For shape 5, the opposite endpoint admits a verified 75-edge partner. All admissible prefixes have been excluded at length 91, while 11 branches remain open at length 90. The earlier result for the displayed **98-edge parent** excludes a 93-edge partner at either end. Its maximum join is also at most 191, with attainment still open. [Ordered witnesses and proof files](opposite.json) · [Independent opposite-end audit](opposite-audit.json) · [Shape 5 prefix coverage](deep-opposite.json) · [98-edge parent proof](../222-prefix-certificates/MATHEMATICAL_NOTE.md)

## Which lengths remain relevant?

For compatible eight-dimensional arms of at most 98 edges each, every join of at least 192 edges can be shortened to exactly 192 while retaining the entire first arm and the crossing. The three unordered arm-length pairs are $(96,95)$, $(97,94)$ and $(98,93)$. Lean checked the prefix construction, preservation of compatibility and this deduction from the two length bounds. The finite parent exclusions above have separate computational proof records. [Lean source](Prefix248.lean) · [Compiler and axiom reports](Prefix248-compile.json)

## Scope and next round

The project interval remains $191\le a(9)\le231$. The contributor's reviewed 231 result has a saved audit at revision 478869ee. The changes from contributor revision 2ecb7a57 to ee9f57e2 affect worker documentation. The independent full dependency rebuild remains pending. [Contributor theorem](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088) · [Subsequent contributor changes reviewed](https://github.com/hironaka-iori/Snake-in-the-box-in-9/compare/2ecb7a57688b9935a403d4bee456874e369cf364...ee9f57e28ff383d4dc9b96a329ae8f44d39ea07b)

**Pause after Round 248.** Continue the same single-crossing construction route when research resumes. Six further recorded 96-edge parents are the next targets for unrestricted 95-edge partners. The marked route includes the three possible arm-length splits and the exact donor indices. The full written-source review remains due at Round 250. [Active route](../../further-research/routes/ACTIVE.md) · [Parent inventory](parents.json) · [Other recorded routes](../../further-research/routes/README.md)
