# Independent review of the total-count semantic pilot

Review date: 3 November 2026. Scope: source inspection, small independent data checks, and verification of completed receipt/source/object/log identities. No solver, Lean compiler, full LRAT replay, or graph computation was run in this review. The initial read-only data check encountered the Windows default text encoding; rerunning with explicit UTF-8 succeeded. Existing proof artifacts and active scripts were unchanged.

No mathematical scope defect was found in the inspected semantic theorem or native RUP replay logic. The completed pilot establishes the semantic interpretation of the selected clauses. The complete Lean contradiction and its composition with the actual-snake transfer remain pending at this review's observation point.

## Completed semantic checks

The two successful receipts were present and independently matched to their current sources, compiled objects, logs and checker hash:

| Module | Recorded elapsed seconds | Printed axiom reports |
|---|---:|---:|
| `Refined115.LocalWindowCnf.Total310` | 39.531 | 0 |
| `Refined115.LocalWindowSat.Total310` | 99.953 | 2 |

The semantic log reports exactly `Snake9.LocalWindow.Total310.check` and `Snake9.LocalWindow.Total310.sat`, each depending only on `propext`, `Classical.choice`, and `Quot.sound`. The CNF module contains definitions; its successful compilation alone is no refutation.

The theorem at `lean/Refined115/LocalWindowSat/Total310.lean:658` takes the existing `Axioms` on the canonical window with transitions $012310$, all five count intervals $[0,21]$, and the additional hypothesis

$$
\sum_{i=1}^{5}\operatorname{absentCorners}(S,v_i,d_i,e_i)\le18.
$$

Its conclusion is satisfiability of the selected CNF. The selected centre records are $(1,0,1)$, $(3,1,2)$, $(7,2,3)$, $(15,3,1)$ and $(13,1,0)$. Thus the sum matches the five internal vertices of $[0,1,3,7,15,13,12]$.

The extra counter is deliberately outside the list subjected to `ctrOK`. Its stored `.ends` kind is not used to derive an endpoint bound. `SumCountSemantics112.sound_append_sum` supplies its numerical bound from the explicit sum hypothesis. The checked permutation is a list permutation, so shared corners retain their multiplicities. The proof of cycle clauses uses `Axioms.acyclic`; no additional unproved cycle exclusion is being supplied.

`TotalGeometry114.actual_total_sum` still has its explicit local-contradiction argument. Once a matching checked `Unsat cnf` is available, the semantic theorem can discharge that argument and yield the actual-snake statement $19\le\sum_{i=1}^{5}\alpha_{r+i}$ for a fitting canonical $012310$ window. This review does not assert that composition is complete or that any global bound has changed.

## Independent finite data checks

An independent inline Python check parsed the generated Lean raw-clause literal, the original full DIMACS formula, the selected input IDs, and the saved variable permutation. All 5,114 generated clauses equal the selected original clauses in their original order after the stated signed-variable renaming and literal encoding. The permutation is a bijection on all 3,129 original variables. The exported record reports 2,139 active variables; this review did not rescan every deduction clause to independently recount the active proof-variable set.

The five corner lists were reconstructed directly from the nine-dimensional adjacency rule and the centre/direction triples. Their concatenation has 105 occurrences and 84 distinct vertices: 68 vertices occur once, 11 twice, and 5 three times. The generated extra counter equals this sorted, renamed list exactly, including repetitions.

All eight appended clauses equal the negative-primary clauses for their recorded vertex lists. Each list was independently checked to be nonempty, distinct, connected and of induced degree two. Only original clause ID 55853, the first of those eight clauses, belongs to this selected core. All six artifacts listed in `total-semantics-plan.json` matched their saved hashes.

## Replay and checker review

`scripts/replay_selected.py:22–40` maps reduced input IDs to their exact original full-formula IDs and moves new deduction IDs above the original input range. Strictly increasing deduction IDs, earlier positive hint IDs and database lookup prevent reuse of an undefined premise. For each deduction, the checker assumes the negation of its clause and requires a conflict after the listed unit-propagation hints. Ignoring an already satisfied hint is sound; an initially tautological deduction is also sound. It requires the final stored clause to be empty and verifies the recorded deduction and hint totals.

The saved replay records 287,753 deductions and 16,816,989 hints against 5,114 selected input clauses. Its script, refinement, original-formula and selected-core hashes were checked. The proof hash agrees with the refinement record; the large proof was not rehashed or replayed in this bounded review. The field `used_input_clauses = 5067` is inherited metadata in this replay script, rather than a separately accumulated replay statistic.

`scripts/check_modules.py` pins the inherited environment receipts, the existing sum-semantics and actual-transfer sources/objects/logs, and direct import objects. Local generated imports require successful matching receipts. Sources and dependencies are checked before and after compilation; successful receipts require exit zero, no timeout, matching printed-axiom counts, and only the three permitted standard axioms. The resolved sum-semantics, counter-soundness and tag objects matched the inspected pins. The semantic receipt retains the CNF receipt, which pins its direct model import. This was a targeted dependency review, not a fresh audit of every inherited object.

One operational issue remains: `check.lock` is created at line 14, while environment validation starts before the `try/finally` at line 48. An early validation exception can therefore leave a stale lock. This affects restart handling and does not invalidate the completed receipts. No active script was changed.

The observed full-export record was still `NATIVE_EXPORT_SIMULATION`, selecting the audited `LratFast15` object with offset 2400 and 21,456 peak slots. That fits its 32,767-slot limit. There was no published `total-plan.json` at inspection. No conclusion about successful simulation, generated full-proof modules or Lean refutation follows from this intermediate record.

## Exact reviewed pins

Paths below are relative to `milestones/115-total-count-certificate`.

| File | SHA256 |
|---|---|
| `scripts/check_modules.py` | `f60462f79a2b1dfa6f7b9fa6ae787eedadb9ab7b5a7570fd57d1c6de2d9e3f2d` |
| `scripts/replay_selected.py` | `02e612b313801b2ee42d3c405279daa453232f403aba34ff4ff7045ee0282f56` |
| `scripts/export_total.py` | `ecdae9d1ea6193dceb534b2e7a5a07f7a447707f0293a2899fca25c08ceea785` |
| `data/refine-core1.json` | `e9772f7b68a47e131e71dd0c4c65c6708859bf0cb630ef53191577137f863c6d` |
| `data/replay-core1.json` | `7438c6097d4c79070769a7bafc588a8b9a1c6314314f7a6305af02b1f06cae52` |
| `data/total-semantics-plan.json` | `65ae09a02682d27ca2f1cd8fc1cf00a782462c9876d0143a6df9dd1540279ac4` |
| `data/total-renumbering.json` | `d954c5b366d606decd31e305ff84622f45e9e2ce92a71ca3900122399b189a29` |
| `data/Refined115.LocalWindowCnf.Total310-audit.json` | `ba573a7ed0d0589bdf0c6a8912d761d7d7c5790e0838f3ed3f82911b3e7bef96` |
| `data/Refined115.LocalWindowSat.Total310-audit.json` | `33c6ce2f12974965e86597163835c3f41aec4cf22be4a9f0baa13fed9094e3cc` |
| `lean/Refined115/LocalWindowCnf/Total310.lean` | `ab31d1a3bdc5b3b06815fa85c39cbc8230b92e07bd1e66d343f477a3a738df9d` |
| `lean/Refined115/LocalWindowSat/Total310.lean` | `ee52d1ad39a1a10a7cd10d88b31297249fc7c45c0c6e3266b55e8dbd21edb52c` |

The mutable full-export progress record is described only as an observation. It is not pinned here as completed evidence.

## Verified checker correction

After the original review, `scripts/check_modules.py` was revised to SHA256 `95a2e0277e316ab3b3f92977b5b7ab2b9d7f167530207b49ab732bc7768e1a7f`. Read-only inspection confirms that lock creation now occurs at line 46, after inherited environment and dependency validation at lines 14–27, immediately before the initial state save and `try` block. This corrects the identified stale-lock risk from failure during that initial validation. The successful semantic pilot was checked by the earlier version, SHA256 `f60462f79a2b1dfa6f7b9fa6ae787eedadb9ab7b5a7570fd57d1c6de2d9e3f2d`; its receipt and the historical hash above remain unchanged. This addendum verifies only that source correction and makes no further claim about full-certificate completion.
