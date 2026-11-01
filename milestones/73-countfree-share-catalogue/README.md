# Count-free share catalogue and global accounting

Checkpoint: 2 November 2026. This task continues the nine-shape proof plan from
[milestone 72](../72-four-count-proof-closure/critical-current/README.md).
The project interval remains **191 <= a(9) <= 235 edges**. The proposed bound
**234 is conditional**. The exact optimum is unresolved.

## Mathematical target

For a snake of edge length \(m\), let \(T\) count singleton-square incidences and
let \(s_0\) count empty square faces. For a vertex \(q\), write
\(e_0(q)\) for the number of empty faces incident with \(q\), and \(d_S(q)\)
for its number of selected neighbours. At a selected vertex \(x\), define

\[
\sigma_M(x)=\sum_{q\sim x}
  \left\lfloor\frac{M e_0(q)}{d_S(q)}\right\rfloor.
\]

The denominator is positive in this sum because \(x\) is selected. A local
window uses six transitions and its five internal vertices. The letters below
stand for pairwise distinct coordinates; the same bound is required when the
transition sequence is reversed. No singleton-count hypotheses are imposed.

| Canonical transition shape | Required five-centre share at resolution 12 | Case | Local Lean theorem |
| --- | ---: | --- | --- |
| 012031 | 16 | 7300 | Checked, including reversal |
| 012032 | 16 | 7301 | Pending |
| 012034 | 20 | 7302 | Pending |
| 012301 | 16 | 7303 | Pending |
| 012304 | 16 | 7304 | Checked, including reversal |
| 012310 | 12 | 7305 | Pending |
| 012314 | 16 | 7306 | Checked, including reversal |
| 012340 | 16 | 7307 | Pending |
| 012345 | 16 | 7308 | Pending |

All nine underlying Boolean refutations were independently checked in milestone
72. They become local snake theorems only after the clause semantics, compact
refutation, geometric interpretation, coordinate normalization, reversal and
axiom audits pass. The machine-readable checkpoint records the completed subset.
The previous distinct-direction theorem proves only share 12, so it does not
discharge case 7308's stronger target.

Cases 7300, 7304 and 7306 pass 71, 108 and 182 modules, with 55, 67 and 88 printed
theorem audits, respectively. The final combined check passes 32 theorem audits
and confirms that the partial catalogue theorem retains exactly the six pending
certificate premises. All audited axioms are confined to `propext`,
`Classical.choice` and `Quot.sound`. The individual cases reuse shared support;
their module counts are not counts of distinct modules across the whole project.

The [coverage theorem](coverage/README.md) is now Lean-checked: every actual
six-transition window has a canonical word in the displayed nine representatives,
or its reversed word does after first-occurrence relabelling. A kernel check over
the restricted-growth enumeration, together with the existing actual-snake
normalization lemmas, proves this universal statement. The enumeration has 203
words and 12 induced orientations. The [generic adapter](adapter/README.md) also
passes Lean: it applies a matching canonical refutation to the actual window in
either orientation, using the universal internal-count bound. A checked
conditional dispatch composes this adapter with coverage and retains all nine
local certificate premises explicitly. The combined integration theorem replaces
completed premises with their checked certificates; its remaining premises are
listed in `data/integration-audit.json`.

The selected nine bounds give a finite comparison graph with exact minimum mean
496 and potential range 600. Its independently checked arithmetic is

\[
496(m-8)-600\le W,\qquad W+4200m\le1098960
\quad\Longrightarrow\quad
m\le\frac{137941}{587}<235.
\]

The graph-to-snake premises remain necessary. The exact graph, potential and
attaining three-cycle are retained in milestone 72; this task does not replace
them with a different model. Same-centre share bounds are combined by their
maximum, so no square share is credited twice by adding alternative rules.

An additional exact audit checks the smallest sufficient bound for each shape
while fixing this graph and potential. It recovers exactly the nine values in
the table. All nine are needed in this restricted certificate: removing or
lowering any one leaves a saved transition inequality unsatisfied. This does
not establish optimality among other potentials or other geometric rules.
The necessary-transition witnesses are in `data/required-shares.json`.

## Current comparison results

Both new comparisons verify all 4,947,008 edge inequalities and an attaining
cycle. Their means use the graph's integer charge units.

| Added local share evidence | Exact mean | Potential range | Comparison bound | Integer bound |
| --- | ---: | ---: | --- | ---: |
| Completed cases 7300, 7304, 7306 and the earlier distinct-direction share 12 | 480 | 536 | 10609/45 | 235 |
| The same rules, additionally assuming share 12 for 012310 | 483 | 551 | 157625/669 | 235 |
| The full mixed nine-shape target | 496 | 600 | 137941/587 | 234 |

The completed additions raise 2,351,884 edge weights and reduce the earlier
potential range from 578 to 536, while a mean-480 cycle remains. The single
additional 012310 premise removes that mean-480 obstruction, but the replacement
mean 483 still gives integer bound 235. It is the next local proof priority.
Receipts are `data/proved-model.json` and `data/assumed-012310x12-model.json`.
Every row still requires the complete graph-to-snake assembly; the existing
unconditional bound 235 comes from the earlier contributor proof.

## Checked global accounting

The [bridge](bridge/README.md) recovers the contributor's identification of the
certificate share with the global square share, pinned at commit
`cd0c90fddf12170d735ee34fcc501e99c60632a6`. The equality is checked for every
snake vertex. In particular,

\[
\sum_{k=0}^{m}\sigma_M(p_k)\le4Ms_0,
\qquad
24T+\sum_{k=0}^{m}\sigma_{12}(p_k)+840(m+1)\le221136.
\]

The second inequality assumes \(m\ge1\). A separate checked overlap lemma gives

\[
\sum_{r=0}^{m-6}\sum_{i=1}^{5}\sigma_{12}(p_{r+i})
\le5\sum_{k=0}^{m}\sigma_{12}(p_k).
\]

For \(m<6\), the window sum is empty. Therefore, for \(m\ge1\),

\[
120T+\sum_{r=0}^{m-6}\sum_{i=1}^{5}\sigma_{12}(p_{r+i})
 +4200(m+1)\le1105680.
\]

These results supply the global share identification and the generic overlap
factor. Matching the finite graph's actual index range, singleton boundary
correction, and potential remains separate work. The recovered share bridge is
credited to the contributor sources; no novelty claim is made.

The graph's window starting at \(r\) charges the singleton count at \(r+8\)
and shares at \(r+4,\ldots,r+8\), with \(0\le r<m-8\). The omitted singleton
indices are \(0,\ldots,7,m\). For \(m\ge8\), their total is at least
\(4+(4+4+4+1)+4=21\): both endpoints contribute at least four, three disjoint
internal pairs contribute at least four each, and the remaining internal count
is positive. Existing checked boundary lemmas therefore justify the constant
\(1105680-4200-120\cdot21=1098960\). Source hashes and exact index matching are
recorded in `bridge/data/accounting-audit.json`. This is an audit of existing
generic lemmas; applying them to the actual graph walk remains required.

## Files and reproduction

- `cases/case73xx/`: isolated generated sources, verification logs and audits.
- `bridge/`: recovered share identity, five-centre overlap, provenance and audits.
- `coverage/`: complete canonical classification and actual-snake coverage.
- `adapter/`: canonical coordinate transfer and conditional catalogue dispatch.
- `scripts/`: generation, replay preparation and archival support.
- `data/`: checkpoint and cross-case verification receipts.

For a case index from 0 through 8, run `scripts/bootstrap_case.py INDEX`, then the
case's `scripts/prepare_lean.py` and `scripts/assemble.py`. Run
`scripts/add_reversal.py CASE`, `scripts/generate_lrat.py CASE` and
`scripts/export_lrat.py CASE`. The case number is 7300 plus the index.

Run the case's `scripts/replay_share.py` for semantic modules. Once that finishes,
`scripts/complete_share.py` checks the remaining modules. Its `--lrat-only` mode
can run alongside the semantic pass, followed by one complete pass after both
finish. Do not run two completion processes for the same case concurrently.
Finish with `scripts/audit_share.py`; only a passing audit establishes the local
theorem. The Windows Lean 4.19.0, pinned mathlib and earlier support builds
recorded by the scripts are required. This checkpoint reuses those dependencies
and does not claim a fresh rebuild of the complete inherited proof chain.

## Remaining obligations

1. Complete the remaining local share certificates and insert them into the
   checked catalogue dispatch. Coverage and the generic coordinate adapters are
   checked.
2. Construct the finite graph walk from an arbitrary snake and justify every
   count exclusion, history state, and share lookup used by that graph.
3. Match the graph's charged centres to the checked path budget and the proved
   boundary estimates.
4. Apply the exact potential to that walk and audit the resulting global theorem.

Milestone 72 also retains six pending count-certificate cases. The nine-shape
route avoids the large additional count-premise list; it does not retrospectively
complete those six cases. The manuscript remains at revision 66, with the next
full rewrite scheduled for milestone 76. Research sources and all three author
names are preserved.
