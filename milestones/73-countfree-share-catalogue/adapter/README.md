# Generic canonical share adapter and conditional catalogue dispatch

The checked module `lean/CanonicalShareAdapter.lean` turns a count-free local certificate into a statement about any matching window of an actual `Snake m`. It supports both orientations.

In namespace `Snake9.CountFreeAdapter73`, the main theorem is `share_bound_of_either_canonical_match`. Its hypotheses are:

- `p : Snake m` and `r + 6 <= m`;
- `canon (dsOf p r 6) = cs` or `canon ((dsOf p r 6).reverse) = cs`;
- `RefutedShare (winOf cs) broadBounds 12 K`, where `broadBounds = List.replicate 5 (0,21)`.

Its conclusion is `K + 1 <= ((List.range 5).map (fun i => coreShare 12 p (r+i+1))).sum`.

Thus a cap-11 refutation yields a share lower bound of 12 for the five internal centres. A cap-15 refutation yields 16 through the same theorem. The coordinate shape is the only matching condition. The count bounds follow from `coreAlpha_le_21`, since all five centres lie strictly inside the snake.

`canonical_share_bound` implements direct matching. It reuses the first-occurrence coordinate realization from `DirectionWindowBridge.window_refute`: `seenAfter`, `idx`, `getD_idx` and `mkPerm_spec`. It then invokes `LocalWindowShareBridge.refuted_share_bridge`.

`reversed_canonical_share_bound` invokes the direct result on `revSnake p` starting at `m-r-6`, then transports the five-centre sum through `dsOf_rev` and `coreShare_window_rev`. `blockList_eq_dsOf` connects the direction representation used by `coverage/lean/SixShapeCoverage.lean` to the representation used here, for any valid block length.

## Conditional catalogue theorem

`lean/ConditionalCatalogueDispatch.lean` imports the checked `SixShapeCoverage` module and composes it with the generic adapter. Its `selectedCap` is 19 for `012034`, 11 for `012310`, and 15 for every other shape. Its `selectedShape` uses the forward canonical word when that word belongs to the nine representatives; otherwise it uses the canonical reverse. `windowLower` is the selected cap plus one.

`catalogue_share_bound` has all nine local `RefutedShare` statements as explicit arguments. Under those premises, it proves that every actual six-transition snake window has five-centre share at least `windowLower`. The lookup is 20 for `012034`, 12 for `012310`, and 16 for the other seven representatives. `windowLower_ge12` proves the lookup is always at least 12, and `catalogue_share_ge12` gives the corresponding share statement under the same nine certificate premises.

The following certificate caps are required, all with bounds `List.replicate 5 (0,21)` and resolution 12:

| Shape | Refuted cap | Resulting share lower bound |
| --- | ---: | ---: |
| 012031 | 15 | 16 |
| 012032 | 15 | 16 |
| 012034 | 19 | 20 |
| 012301 | 15 | 16 |
| 012304 | 15 | 16 |
| 012310 | 11 | 12 |
| 012314 | 15 | 16 |
| 012340 | 15 | 16 |
| 012345 | 15 | 16 |

These remain premises. This module imports no individual LRAT certificate and does not assert that every listed certificate has been completed. The printed theorem signatures in the compiler log expose all nine arguments; the audit checks their presence in both main conditional conclusions.

## Verification and provenance

Run the scripts in this order using Python: `scripts/prepare_support.py`, `scripts/check.py`, `scripts/audit.py`. The check compiles both modules sequentially with at most one Lean 4.19.0 process. The audit records exact source, object and log hashes in `data/proof-audit.json`; its required status is `PASS_CONDITIONAL_CATALOGUE_DISPATCH`, with `generic_adapter_status` retaining `PASS_GENERIC_CANONICAL_SHARE_ADAPTER`.

The ten printed theorem axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`. The new source and pinned support sources have no proof placeholders or native decision shortcut.

Nine normalization modules are pinned against the existing milestone32 normalization receipt, with the maintained sources checked for LF-equivalent content. The local-share bridge is pinned against the successful milestone72 `critical-current/share-proof/data/proof-audit.json` receipt. `SixShapeCoverage` is pinned against milestone73's successful coverage receipt. `data/support.json` identifies the eleven exact inherited compiled objects and historical successful logs, with hashes. Their source snapshots are retained under `upstream/`. These dependencies were reused; this task does not claim to have rebuilt the entire inherited library.

## Scope remaining

Each completed local case must supply its displayed `RefutedShare` premise, with definitional conversion if its named window and bounds are expressed differently. The coverage-to-share composition is checked conditionally; discharging all nine certificate premises remains separate. The history-graph interpretation, per-edge lookup and global numerical upper bound remain separate obligations.
