# Independent weight-model audit

The independent reconstruction passed on all 4,947,008 saved full keys in 791 contexts. There were no endpoint, source-weight, completed-profile, or conditional-floor18 mismatches. The numerical check took 2.078 seconds, below the 300-second budget. No solver, Lean compiler, local proof replay, or potential search was run. Existing milestone files were read without modification.

Evidence is saved in `data/weight-model-audit.json`; its `source_files_sha256` pins every inspected builder, table, graph, and result used in the numerical comparison. `scripts/audit_weight_model.py` imports NumPy only, with no builder or discovery-module imports. It reconstructs credits directly from the recorded tables and the explicit count-conditioned rules. The script also records its own SHA-256. This is a finite-array reconstruction check, with the remaining semantic and defined-graph obligations stated below.

## Full keys and exact formula

A row is the ordered triple `(d,q,c)`: direction ID, current history ID, six-count code. Its bounds are $d<505$, $q<75$, and $c<46656$. All saved full keys were checked to be distinct and strictly increasing in this order. No reduction to an endpoint pair or acceptance-class ID is valid for the weight definition.

Let $b_0,\ldots,b_5$ be the six base-six digits of $c$, increased by one, with $b_0$ most significant. For the chosen count-free floor profile $F$, the exact builder formula is

$$
w_F(d,q,c)=120b_5+\max\{G(d),C(d,c),H(d,q,c),J(d,c),F(s(d))\}.
$$

Here $s(d)$ is the lexicographically smaller of the canonical last-six-transition word and its canonical reversal. Every absent credit contributes zero. The stored credits already use the scale in `coreShare 12`; they must not be multiplied by 12 again. All five alternatives bound the same five-centre sum, so their sum is unsupported.

The exact components are:

- $G(d)$: `59-extended-share-window/data/geometry.json`, `patterns[d].share_lower`. Each of the 505 direction words was checked against the corresponding `extensions[d]` in the extended model.
- $C(d,c)$: the maximum applicable credit from the following eight oriented rules. Test the canonical last six transitions in the indicated orientation and the last five symbols $b_1,\ldots,b_5$ exactly. The five-symbol code is $c\bmod7776$.
- $H(d,q,c)$: append $d$ to the recorded history prefix `prefixes[q]`. For each matching last-three signature among the 55 share rules in milestone67, include its `geometric_lower` regardless of caps; include `lower` only if every recorded `caps[k]` bounds $b_k$. Take the maximum over all applicable alternatives. The three exclusion rules affect retention and add no credit.
- $J(d,c)=120$ when the last six transitions are distinct and the last five symbols are $(4,5,4,2,6)$ or $(6,2,4,5,4)$; otherwise it is zero.
- $F(s(d))$: the appropriate column in the profile table below.

| Oriented six-transition shape | Five symbols | Credit | Saved matching edges |
| --- | --- | ---: | ---: |
| 012314 | 3,3,3,6,5 | 48 | 111 |
| 012345 | 3,6,2,3,6 | 96 | 458 |
| 012034 | 6,3,6,3,3 | 96 | 474 |
| 012345 | 4,6,2,3,6 | 96 | 531 |
| 012314 | 5,6,3,3,3 | 48 | 348 |
| 012345 | 6,3,2,6,3 | 96 | 819 |
| 012342 | 3,3,6,3,6 | 96 | 176 |
| 012345 | 6,3,2,6,4 | 96 | 819 |

The final four rows reverse both the original direction word and its count symbols, then canonicalize the reversed direction word. In particular, the reverse of 012034 has canonical shape 012342. Using the unoriented shape $s(d)$ for these conditioned tests without also reversing counts would be incorrect. The share-120 test matched 1,280 saved edges. Every one of the 55 history share rules emitted on saved rows; all three exclusion signatures emitted, and no retained row satisfied their exclusion caps.

## Profiles and numerical agreement

| Shape | Completed floor | Conditional floor18 |
| --- | ---: | ---: |
| 012031 | 16 | 16 |
| 012032 | 0 | 16 |
| 012034 | 0 | 18 |
| 012301 | 0 | 16 |
| 012304 | 16 | 16 |
| 012310 | 12 | 12 |
| 012314 | 16 | 16 |
| 012340 | 0 | 16 |
| 012345 | 12 | 16 |

Zero means no added count-free credit. It does not suppress the other components. The completed 012345 floor12 uses the existing distinct-direction result. The stronger conditional profile still needs its five unfinished local inequalities, now with floor18 rather than20 on 012034. A hypothetical refutation used to establish floor18 needs the share cap17; the older floor20 target uses cap19.

For each of the 4,947,008 rows, the independent base reconstruction was compared directly with the source array. Each profile was then compared with the source-array update used by the historical workflow, and its entire little-endian int64 weight array was hashed. Both hashes equal the previously recorded results:

| Profile | Weight SHA-256 | Edges raised from source |
| --- | --- | ---: |
| Completed | `8ff4c8c57709e973371f0825c1866d6e10293c5f47de19d4005fa7cf5ecd5eba` | 2,536,591 |
| Conditional floor18 | `355e32a575ba57f17f259952cfd2d2766e1dbe7619ef78102a241e1b35fdde1f` | 4,186,261 |

The completed profile has no standalone saved graph array in this workflow; its original whole-array hash is in milestone73 `data/proved-model.json`. Floor18 likewise has its whole-array hash in milestone97 `floor-sensitivity/012034-minimum/floor18.json`. As an additional independent cross-check, the reconstructed original conditional floor20 profile and all five nonweight columns were compared directly against the saved full20 graph; all entries matched.

The old results report slope483/range551 for the completed profile and slope496/range602 for floor18. Those potentials were not rechecked in this audit. The milestone97 check already establishes floor18 as the least feasible integer floor when only that floor varies in this fixed graph and boundary argument. It does not establish a universal local share floor or a new global snake bound. The saved seven-edge path has weight2872 under floor18 and does not certify that range602 is optimal.

## Endpoint and actual-snake interpretation

With $B=7776$ and $N=1026432$, define

$$
\operatorname{state}(s,q,a)=
\begin{cases}sB+a,&q=0,\\N+(q-1)B+a,&q>0.\end{cases}
$$

The source and target are

$$
U(d,q,c)=\operatorname{state}(\operatorname{sourceId}(d),q,\lfloor c/6\rfloor),
\qquad
V(d,q,c)=\operatorname{state}(\operatorname{targetId}(d),\operatorname{builderNext}(q,d),c\bmod B).
$$

The script independently reconstructed both columns on every saved key, including the longest matching history-prefix update and source/target compatibility. The state space has 1,601,856 raw positions. Potential values must use this numbering unless a checked remapping is supplied.

For an actual snake and $r+9\le m$, the six symbols correspond to truncated counts at vertices $r+3,\ldots,r+8$. The five-centre share sum is

$$
S_r=\sum_{i=0}^{4}\operatorname{coreShare}(12,p,r+i+4).
$$

Each symbol below6 means an exact count; symbol6 means the interval $[6,21]$. Saturation must be preserved in every concrete refutation. A history cap at index $k$ concerns the actual centre $r+k+3$; its existing upper caps are below6. A matching eleven-transition history window starts at $r-2$, so its offsets6 through10 agree with centres $r+4$ through $r+8$.

The shortest semantic bridge is to bound every component of the maximum by $S_r$, then use the entering-count identity and truncation inequality. Milestone97 already supplies `GeometricCredit97.actual_geometric_history_credit` and `actual_geometric_history_weight`. Its `SymbolCredit97.encoded_forward_suffix_share` and `encoded_reversed_suffix_share` supply the generic conditioned-rule transfers, retaining concrete refutations as premises. Milestone98 must instantiate those premises in the current environment, include the share-120 rule, and combine the selected count-free profile. The resulting target is

$$
w_F(\operatorname{directionId}(p,r),\operatorname{actualHistory}(p,r),\operatorname{sixCode}(p,r))
\le120\operatorname{coreAlpha}(p,r+8)+S_r.
$$

For the completed profile no unfinished count-free premise should remain. For the conditional profile the five remaining local floor inequalities must remain explicit. This audit does not inspect or certify concurrently written milestone98 Lean modules.

## Defined-graph obligation and next check

`Enumeration87.Row` is exactly `(d,q,c)`. In milestone92 `DefinedProofGraph.lean`, `diagramKeep` selects a recorded acceptance class from the block number $75d+q$; missing blocks reject. `rows` enumerates every bounded key accepted by that diagram. `Assembly87.rowSource` and `rowTarget` give the endpoint formula above.

`DefinedGraph92.defined_graph_covers` proves one-sided coverage under `ClassMembershipFamily g` and the finite assignment-check premise. It allows conservative extra accepted rows. `defined_actual_walk` additionally requires the two reference-refutation catalogues, and exposes endpoint equalities only. Weight transfer must preserve the actual full key: use `Assembly87.actual_saved_edge`, which retains that key equality, or add a key-preserving counterpart to the defined walk. Endpoint equalities alone do not identify a key-dependent weight.

The next necessary finite check is therefore, for every bounded key accepted by the defined diagram,

$$
P+\pi(V(d,q,c))\le D\,w_F(d,q,c)+\pi(U(d,q,c)),\qquad D>0,
$$

together with the potential range on all raw states. This must include every conservative extra row. The present saved-key agreement proves neither the absence of extras nor their inequalities. Shared acceptance classes can reuse code enumeration, but each context still has its own endpoints and credits. A proof reducing all contexts to the 791 recorded blocks must also justify the successful block-lookup correspondence; the bound $q<75$ is required for the block encoding.

There were no mathematical or numerical failures in the reconstruction. During source inspection, two guessed historical folder names were absent; exact paths were located with a file search before any input was used. The stated numerical runtime covers the sole reconstruction run. No accepted-diagram enumeration, independent new potential check, local refutation, compiler audit, or global-bound claim is included.
