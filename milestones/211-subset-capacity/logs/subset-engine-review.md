# Subset-capacity source review

Date: 2026-11-14. Scope: the new native engine, its source generator, and continuation wrapper, compared with the frozen round-209 sources and current handoff. No compiler, search, Lean, software test, or proof replay was run by this reviewer. Only this report was written.

Result: no soundness defect found in the new subset rules under the inherited all-different clique assumptions. The new pruning is confined to the declared clique. The separately required transfer of the seven frozen frontier entries was not yet part of the inspected evidence; subsequent search results are outside this source review.

## Mathematical justification

For a subset \(S\) of pairwise unequal variables, let \(U=\bigcup_{x\in S}D_x\), where \(D_x\) is its current domain. Any satisfying assignment gives an injection from \(S\) into \(U\). Hence \(|U|<|S|\) excludes that branch. If \(|U|=|S|\), the assigned values of \(S\) exhaust \(U\), so every other variable in the same all-different clique must avoid \(U\). An outside variable may be pruned by this argument only if it is known unequal to every member of \(S\).

The last qualification matters here: nine variables outside the clique may share words with their declared partners. The implementation correctly limits the removal loop to `j < cap_count`, excluding members of the selected subset. It does not remove the union from all 81 model variables. The old partner-support rule remains separate and unchanged.

After a perfect matching, direct arcs from a variable to the matched owner of each word in its domain produce a useful subset. A reachable set is closed under these arcs. Its domain union is contained in the matched words belonging to that set; conversely each matched word belongs to its owner's domain. The union therefore has exactly the set's cardinality. This establishes why the reachability construction discovers tight sets. Correct rejection and pruning still rely on the explicit domain-union calculation, rather than trusting this discovery property alone.

## Implementation inspection

- `capacity_solver.c:62–95`: augmentation records reached variables and words. On failure, the engine recomputes the complete union of the reached variables' actual domains and returns a contradictory branch only after verifying a strict cardinality deficit. Failure to obtain such a witness calls `fail`, exits nonzero, and cannot be committed by the wrapper as an exhausted subtree.
- Lines 98–115 validate the successful matching: every occupied word maps to an in-range clique index, no clique index repeats, its assigned word lies in that variable's domain, and all clique variables are matched. The input already restricts all clique domains to the declared alphabet, whose cardinality equals the number of clique variables. Consequently every declared word has an owner. An unowned domain word triggers an error.
- Lines 106–118 implement reflexive reachability and the usual bitset transitive closure. Lines 119–135 recompute each chosen set's current domain union. A strict deficit rejects; equality permits pruning; other cardinalities are skipped. The full clique is skipped because there is no other clique member to prune.
- Earlier removals within the same call can make the stored reachability relation stale. This does not invalidate subsequent deductions: membership still specifies a subset of distinct clique variables, and the union and cardinalities are recomputed from the current domains immediately before use. Within one removal loop only variables outside that subset change, so its recorded union remains current.
- Every removal is an intersection with the complement of the reserved union. Empty domains reject, and each nonempty change enqueues its binary neighbours and sets `altered`. The outer propagation loop therefore revisits binary, old capacity, partner, and subset constraints until no domain changes.
- The input guard now requires `cap_count <= DMAX`, with `DMAX = 64`. Thus variable-set shifts use indices 0 through 63, `reach[64]` is sufficient, and word shifts also stay within 64 bits. Every trailing-zero operation is guarded by a nonzero mask. `cap_vars` remains a distinct validated list. Owner indices originate in that list and are checked before constructing reachability.
- The exact textual diff against round 209 changes only subset helpers/counters, their propagation call, the tighter clique-size guard, and the added output counters. The branching order, subtree traversal, stop handling, saved pending domains, input relation format, old capacity rules, and solution output remain unchanged. Output adds `subset_calls`, `subset_removals`, `subset_failures`, and `tight_sets`; these are observational counters and are not used to justify exclusions. `tight_sets` counts encountered tight sets, including repeated encounters, rather than distinct mathematical subsets.

## Continuation and retained assumptions

The new wrapper's complete diff changes its introductory description and removes the old initial model-generation branch. It now refuses to start without an existing explicitly transferred state. Its `one_job` implementation, witness verification, pending-domain containment/disjointness checks, state replacement, and resource policy are unchanged. Nonzero engine exits leave the old state uncommitted. Engine/model hashes are rechecked before accepting an output.

The frozen input's clique and outside-nonpartner inequalities were established from the original binary tables in round 209. The current source review reread that construction and confirmed the old source hashes. It did not repeat the 22,208 binary diagonal-entry comparisons already documented in `209-slice-capacity/logs/capacity-chain-review.md`. The C parser validates structure and ranges, but does not itself establish those inequalities. Because round 211 removes model generation, its explicit transfer must preserve the exact model, permutations, input tail and capacity declaration, and retain the original frontier without discarding or modifying a region. Changing engine hashes alone does not establish that transfer.

The existing operational assumptions remain: Python assertions enabled, one coordinator, and no concurrent mutation of pinned inputs. The lock creation is not atomic, and the resource monitor does not independently exclude every possible native worker. These are inherited execution conditions, with no new claim of parallel safety or power-loss durability. Source inspection gives no performance comparison, exhaustive matching implementation certificate, native traversal certificate, actual-snake exclusion, or improved global bound.

## Exact SHA-256 pins

Paths below are relative to `E:/Snake-in-a-box/`.

| File | SHA-256 |
|---|---|
| `milestones/211-subset-capacity/scripts/capacity_solver.c` | `54aef14e94221646ffe5851a7e4ec0a6a43700bbc1f4f66c024f5dc51f6aeea4` |
| `milestones/211-subset-capacity/scripts/capacity_continue.py` | `3a4456d34ce204769201c50c19cd35a2c71804698c449358e7f083a2dc992e46` |
| `milestones/211-subset-capacity/scripts/prepare_engine.py` | `e15f7a62ef4344e3e296986c367fb7aebd47200dfd68de44cfefaf453b57ca89` |
| `milestones/209-slice-capacity/scripts/capacity_solver.c` | `2a4e12272665b3bcac59a32c64d7167e5e343f1174d0592f5945717e2e0f593e` |
| `milestones/209-slice-capacity/scripts/capacity_continue.py` | `6aa8325cb39a963d7e21bc6f1f2e720016fedf312f97af5d0b5e21a44b50e67b` |
| `milestones/209-slice-capacity/data/case-23/state.json` | `ec3701961111ed7af971295d4512853adaa4f26dc120bc559e70e39b4176d32e` |
| `milestones/209-slice-capacity/data/case-23/capacity-constraints.json` | `b0ff9653b522574b4e51219d355d6337a47039633f4c371333ef95376c72df91` |
| `milestones/209-slice-capacity/logs/capacity-chain-review.md` | `15387be3a5d7d7af84b56d6b8089d4af5b992921180104bd5b8bdbeae0e6fceb` |
| `handoff/CURRENT_STATUS.md` (round-210 stopping point) | `948a4c87256f368ee7729a7a2685f48f646ecb111c260ba43837d3d866b649b5` |

The generator was inspected as source; it was not executed by this reviewer. Its unique-replacement guards, new helper text, clique-size guard and wrapper slicing agree with the observed source diff. The handoff remains a round-210 snapshot at this review cutoff. The parent controls subsequent compilation, transfer and execution records.
