# Weight and potential interface for the defined graph

Audit date: 3 November 2026, Japan time. This is a bounded source and receipt audit. No Lean compiler, solver, graph builder, or replay was started. The statements proposed below are obligations, not newly checked theorems.

The main missing semantic theorem is that the credit attached to an actual **full edge key** is bounded by the share of its five specified centres. The existing global charge and potential-telescoping arguments can then be reused. Defining the graph by its acceptance diagram removes the need to identify an external row array, provided the weight and potential checks use that same defined graph.

## Exact key, counts, and raw state numbers

Use a key `(d,q,c)` in precisely the order defined by `Enumeration87.Row`: direction ID, current history ID, six-count code. Its bounds are $d<505$, $q<75$, and $c<46656$. Two keys with the same source and target remain distinct. Likewise, two contexts assigned the same acceptance class can have different weights and potential endpoints.

Write $B=6^5=7776$, $N=132B=1026432$, and

$$
\operatorname{state}(s,q,a)=
\begin{cases}
sB+a,&q=0,\\
N+(q-1)B+a,&q>0.
\end{cases}
$$

The raw state space has $1601856$ positions. The endpoints are exactly

$$
U(d,q,c)=\operatorname{state}(\operatorname{sourceId}(d),q,\lfloor c/6\rfloor),
\qquad
V(d,q,c)=\operatorname{state}(\operatorname{targetId}(d),\operatorname{builderNext}(q,d),c\bmod B).
$$

These are `Assembly87.rowSource` and `rowTarget`, using `GraphWalk78.edgeSource` and `edgeTarget`. A potential table must retain these raw numbers. A compact numbering needs its own checked decoding equality; acceptance-class numbers are not state numbers.

For a snake of $m$ edges and a fitting edge start $r+9\le m$, put $b_j=\min(6,\alpha_j)$. The actual key uses the canonical nine-direction word at $r$, the history obtained from the initial empty history, and

$$
c_r=\operatorname{encode}(b_{r+3},\ldots,b_{r+8}).
$$

The source stores the first five symbols and the target stores the last five. `GraphWalk78.sixCode_spec` already proves the division, remainder, entering-count, and range identities. In particular, $c_r\bmod6+1=b_{r+8}$.

Every occurrence of symbol $6$ denotes the count interval $[6,21]$, never the equation $\alpha_j=6$. `GraphInterpretation75.truncated_guard`, `unsaturated_exact`, and `saturated_interval`, together with `coreAlpha_le_21`, supply the needed translations. Current history cap values are $1,2,5$, so their upper-cap guards are below saturation. The five-count forward share rules and the share-120 rule must retain the full intervals at their saturated positions.

## Exact weight reconstruction

The inspected builders define

$$
w(d,q,c)=120(c\bmod6+1)+L(d,q,c).
$$

All credit values below use `coreShare 12`; the factor 12 is already present in that share definition. Do not multiply the saved credit values by 12 again. The coefficient 120 is the coefficient of the entering truncated singleton count.

The credit $L$ is a maximum, with zero as a safe default for an inapplicable rule, over the following alternatives:

1. The nine-transition geometric credit `geometry.json["patterns"][d]["share_lower"]` from milestone59.
2. The four forward count-conditioned rules and their reversals in milestone70. Their direction test uses the last six transitions, and their count test is `c % 7776`, corresponding to centres $r+4,\ldots,r+8$. The forward triples are `(012314,[3,3,3,6,5],48)`, `(012345,[3,6,2,3,6],96)`, `(012034,[6,3,6,3,3],96)`, and `(012345,[4,6,2,3,6],96)`.
3. Every emitted history share rule. There are 55 share rules and three separate exclusion rules in the inspected `full-model.json`. On a signature match the geometric credit applies without the count-cap test; the stronger `lower` credit applies only when all recorded caps hold. Each applicable alternative enters the maximum.
4. The milestone72 share-120 update: the last six directions are distinct and the last five count symbols are `[4,5,4,2,6]` or their reversal `[6,2,4,5,4]`. Its credit is 120, in the same units as the other credits.
5. The chosen count-free floor profile, selected from the canonical last-six-direction shape up to reversal.

This formula is read directly from `70-proof-supported-share-model/scripts/build.py`, `72-four-count-proof-closure/critical-current/scripts/prepare.py`, and `countfree_effect.py`. The ten interval filters change retained rows; they do not add a share term. Alternative local credits refer to the same five-centre share total. Their sum has no justification here.

For a new Lean weight definition, use explicit bounded lookups and reproduce every signature, cap, orientation, and default case. Pin the literal tables and prove the correspondence to the intended profile. If instead an existing weight array is reused, equality to this key-indexed function is an additional obligation; a common source/target pair is insufficient to select its weight.

## Completed and conditional floor profiles

The current `73-countfree-share-catalogue/data/integration-audit.json` reports completed cases 7300, 7304, 7305, and 7306. Their final local receipts exist and report `PASS_LOCAL_SHARE_THEOREM`. Cases 7301, 7302, 7303, 7307, and 7308 have no final `proof-audit.json` at this inspection. The active case7302 replay is therefore still a premise.

| Shape | Completed added floor | Full target floor |
| --- | ---: | ---: |
| 012031 | 16 | 16 |
| 012032 | 0 | 16 |
| 012034 | 0 | 20 |
| 012301 | 0 | 16 |
| 012304 | 16 | 16 |
| 012310 | 12 | 12 |
| 012314 | 16 | 16 |
| 012340 | 0 | 16 |
| 012345 | 12 | 16 |

Zero in this table means no added count-free floor; the geometric and count-conditioned alternatives remain available. The distinct-direction floor 12 comes from the earlier checked share-12 theorem, not case7308's stronger target.

`CatalogueIntegration73.partial_catalogue_share` already removes the four completed case premises and retains exactly the other five. `GraphInterpretation75.graph_catalogue_share_bound` establishes the exact graph-suffix orientation and centre indices, but its current interface retains all nine certificate arguments. Instantiate completed arguments or compose it with the partial catalogue theorem; do not silently remove the five pending arguments.

The inspected completed-profile metadata records slope 483 and range 551; the full mixed target records slope 496 and range 600. These are finite-array results. Neither transfers to `DefinedGraph92.rows` merely because the acceptance diagrams were constructed from the old graph. Recheck the potential inequality on the defined rows with the exact chosen weight profile. A certificate for larger conditional weights does not establish the inequality for smaller completed-profile weights.

## Minimal block certificate

Fix natural numbers $P,D,R$ with $D>0$, an explicitly defined weight function $w(d,q,c)$, and a total potential function $\pi$ on the raw state numbers. For each recorded context $(d,q)$, the needed block statement is

$$
\forall c<46656,\quad
\operatorname{diagramKeep}(g,d,q,c)=\mathrm{true}
\quad\Longrightarrow\quad
P+\pi(V(d,q,c))\le D\,w(d,q,c)+\pi(U(d,q,c)).
$$

Check **every code accepted by the defined diagram**, including any conservative extras. The witness-cover theorem proves that retained actual codes are accepted; it does not prove that diagram acceptance is equivalent to the original numeric retention predicate. Checking only the old retained-array codes therefore leaves a gap.

There are 791 recorded contexts and 127 distinct acceptance classes in the assignment data. Shared code diagrams can reduce enumeration work, but a class-level proof cannot discard the separate context: $U,V,L$ can depend on both $d$ and $q$. To reduce all bounded contexts to the 791 recorded blocks, prove that a successful `savedBlockClass (75*d+q)` lookup identifies the corresponding saved block entry. Missing blocks already reject by definition. Keep the bound $q<75$, which makes the block encoding injective.

The potential range obligation can be the simple global statement $0\le\pi(s)\le R$ for every raw state $s<1601856$. A sharper endpoint-specific difference bound is also sufficient, but requires its own theorem about actual initial and final states. If a balanced lookup replaces a list lookup, prove equality of the total lookup functions, including defaults; a Python equality check does not provide this Lean equality.

`CriticalFamily61.edge_of_check` gives the generic finite-inequality extraction. Its `path_bound` telescopes an open walk:

$$
P(m-8)\le D W+R,\qquad W=\sum_{r<m-8}w(d_r,q_r,c_r).
$$

No closed-cycle assumption is required. A minimum-cycle-mean computation alone does not supply the finite open-walk bound or the potential range.

## The most important missing theorem

Define the actual five-centre share total

$$
S_r=\sum_{i=0}^{4}\operatorname{coreShare}(12,p,r+i+4).
$$

The priority theorem, provisionally named `actual_credit_le_five_centre_share`, should prove

$$
L(\operatorname{directionId}(p,r),\operatorname{actualHistory}(p,r),
  \operatorname{sixCode}(p,r))\le S_r
\quad(r+9\le m),
$$

under exactly the unfinished local-floor premises of its selected profile. It immediately gives the required weight inequality by `sixCode_spec`.

The largest unresolved component is the dispatch of the 55 history share rules over **all** compatible eleven-transition words. `History84.emitted_three_actual` proves that a three-ID emission cannot occur at $r=0,1$. `emitted_three_canonical_slices` identifies the three overlapping nine-windows of `canon (dsOf p (r-2) 11)`. It does not prove credit coverage for the 55 share rules. The milestone84 concrete variant work covers the three exclusions, which is a different statement.

For each emitted share signature, prove that the actual canonical eleven-word lies in its complete compatible-variant list. Then dispatch the local geometric/count-conditioned credit for that variant and prove the recorded rule credit is no larger than the minimum applicable variant bound. `67-critical-family-charge/scripts/build_full.py` uses this minimum explicitly. Of the 58 recorded rules, 47 carry a `variants` field and 11 do not; the absence of that field does not prove a signature has a unique realization. Audit completeness for every share rule, including those stored with only `directions`.

The eleven-word begins at $r-2$. Its share-centre offsets 6 through 10 become $r+4,\ldots,r+8$. Its cap on six-count position $k$ concerns the actual count at $r+3+k$, hence eleven-window offset $5+k$. These two offsets must not be interchanged. Milestone61/67 `in_snake` lemmas already provide the local five-centre conclusion after a coordinate-frame match; canonical-frame dispatch and complete variant membership remain necessary.

For the other credit families, reuse `ExtendedShare59.credit_in_snake`, the existing count-conditioned `RefutedShare`/geometry bridges with their exact intervals, and `GraphInterpretation75.actual_suffix_lookup`. Once each applicable candidate is bounded by $S_r$, a finite maximum is bounded by $S_r$. No new empty-square incidence argument is required.

## Preserve the full key when connecting to the actual walk

`DefinedGraph92.defined_actual_walk` returns endpoint equalities but omits the row-key equality from its conclusion. It is sufficient for an endpoint-only walk and insufficient by itself for selecting a key-dependent credit. Use `Assembly87.actual_saved_edge`, with `defined_graph_covers` and `defined_endpoint_columns`, to obtain the stronger witness

`rows[i]? = some (directionId p r, actualHistory p r, sixCode p r)`.

Alternatively, work directly with the actual key and the block theorem, using `actual_source_state` and `actual_target_state`. This avoids allocating or identifying an edge-indexed weight array. The finite assignment theorem is now checked; `ClassMembershipFamily g` and the two explicit reference-catalogue refutation premises remain in the generic actual-graph interface until their own closures are supplied.

## Global accounting after the bridge

For $m\ge8$, use `BoundaryCharge67.discarded_counts` with the entering counts $b_{r+8}$. The discarded indices $0,\ldots,7,m$ contribute at least 21 singleton counts. Use `ExtendedBudget59.window_budget` with offset 4 for $L(d_r,q_r,c_r)\le S_r$. Together with `CountFreeBridge.core_share12_charge_le`, these give

$$
W+2520\le5(24T+\Sigma),\qquad
W+4200m\le1098960.
$$

`CountGeometry78.localAlpha_eq_coreAlpha` supplies the existing representation bridge needed for the singleton hypotheses. Handle shorter snakes separately before using $m-8$ in integer arithmetic. `BoundaryCharge67.aggregate_charge` and `global_charge` already check the arithmetic; the older milestone59 bound discards only 15 counts and should not replace this stronger boundary estimate accidentally.

Combining the potential and charge inequalities yields

$$
(P+4200D)m\le1098960D+8P+R.
$$

For $P=496,D=1,R=600$, the resulting strict comparison at $m=235$ has margin 32. That conclusion still depends on the weight bridge, the defined-graph potential check, graph coverage, and the five pending count-free certificates. It is not a new bound from this audit.

## Evidence checked and limits

The following source, object, and log bytes were compared with their existing successful receipts during this audit; all matched. No dependencies were rebuilt.

| Interface | Receipt SHA-256 |
| --- | --- |
| `92/data/DefinedProofGraph-audit.json` | `730dcf8ed7510d91e084ee1ff82ef9807074b14d499c9abef8b9e90160d3593e` |
| `84/data/HistoryWindow-audit.json` | `0078c844ad8ad57517b3f800e33ac3c776848e7d2c9325b4adb9ab3f348e99ab` |
| `78/data/StateWalk-audit.json` | `48bd2a78950b5d3e2a3fd2bff026e8b487f0fdff0744368e91fdf3d2cd870363` |
| `75/lookup/data/proof-audit.json` | `08d40929a73eacb66551e311eb271ef6fc524a5f882faef6c0c209b9f68689ad` |

Milestone numbers in the table abbreviate the existing milestone directory names. The milestone59,61,67 receipt hashes and selected `ExtendedShareBridge`, `ExtendedBudget`, `FinitePotential`, and `BoundaryCharge` source hashes were also rechecked against milestone74's saved interface audit and matched. This does not replay their dependency closures. The current combined local-catalogue receipt has SHA-256 `d90a4c77464c10db1d62a8b70cb7f14bb15fac5162ca01255128fd727d5d1d01`; its five pending cases were checked against the presence or absence of their final local receipts.

Suggested implementation order: define the two weight profiles and their exact lookups; prove the per-candidate credit dispatch, prioritizing complete history-variant coverage; combine credits by maximum; check the block potential inequalities and range on the defined graph; assemble the existing charge and open-walk bounds. The finite potential check and semantic credit bridge are independent obligations. Both are required for an upper bound.
