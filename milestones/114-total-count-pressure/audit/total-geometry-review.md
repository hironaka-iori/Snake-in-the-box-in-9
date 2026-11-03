# Total-count geometric transfer

`Snake9.TotalGeometry114.actual_total_sum` passed Lean 4.19.0 on the first attempt in 88.797 seconds. The only printed axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The source introduces no definitions and contains no `sorry`, `admit`, or `native_decide`.

## Exact statement and limitation

For a genuine snake $p$ and $r+6\le m$, assume its six directions starting at $r$ canonicalize to $(0,1,2,3,1,0)$. The theorem concludes

$$
19\le \alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}+\alpha_{r+4}+\alpha_{r+5}.
$$

This conclusion retains the explicit argument `hlocal`: every Boolean local assignment satisfying `Axioms` for `winOf [0,1,2,3,1,0]`, with all five count intervals $[0,21]$, contradicts a total of at most 18 over its five specified absent-corner counts. No concrete local refutation is imported. Consequently this receipt checks the transfer from that local contradiction to actual snakes; it does not establish the local contradiction, eliminate graph keys unconditionally, or improve a global snake bound.

The window vertices are $(0,1,3,7,15,13,12)$. The five centre/direction records are $(1,0,1)$, $(3,1,2)$, $(7,2,3)$, $(15,3,1)$, $(13,1,0)$. All five records appear once in the local sum. Reused canonical-frame machinery maps these counts to actual positions $r+1$ through $r+5$. The existing bound `coreAlpha_le_21` supplies each upper bound; nonnegativity supplies each lower bound. No extra central cap is required.

## Reused proof and verification environment

The proof adapts the checked 112 outer-sum and 113 pair-sum transfers. It imports the existing `CanonicalExclusions`, `JointCountBridge`, and `LocalWindowTags` objects, using `actual_canonical_frame`, `mkPerm_spec`, `frame_axioms`, and `JointTags.frame_count`. Kernel checks verify the concrete window and its six direction labels. The final arithmetic step contradicts `hlocal` after rewriting all five count equalities.

The checker pins the successful 113 `PairGeometry113` receipt, all its recorded dependencies, and its source, object, log and source snapshot. It also rechecks the inherited 112 isolated environment and direct 79/81/111 dependencies, executable hashes, and source/checker hashes before accepting the new object. Its process gate permits at most one other Lean process with aggregate private memory below 8 GiB; the observed other process was the parent's conditional 104 retry. No old dependency was compiled or modified. The successful attempt has exited, releasing this helper's compiler slot.

## Saved evidence

All paths below are relative to `milestones/114-total-count-pressure`.

| Artifact | SHA-256 |
|---|---|
| `lean/TotalGeometry114.lean` | `c0ff807395dd2d1c53eabb05f13a7d8a53632477ad680be251359b75ace02518` |
| `scripts/check_total_geometry.py` | `a6b88e18d839e6320ff1a1d7d1231b3db502f45bc7790595a76acae0217d6402` |
| `build-total-geometry/TotalGeometry114.olean` | `2b0c3bc8838e0f7f596d03bc271f3f49dbd41e2283c5b316765596c28165fe85` |
| `logs/TotalGeometry114-1793664595755628100.log` | `d516eae40e6f496925535f4ab98e5e73f6982ba1b8675bd340f34cf8bb1ae26e` |
| `data/TotalGeometry114-audit.json` | `6975b1a3057a32d3bbd6327a184afc4b87f2630cc10c0ee3810933c163a25d6b` |

The same run preserves immutable source/checker snapshots and its complete record under `logs/TotalGeometry114-1793664595755628100-*`. There were no failed compiler attempts or source repairs in this task.
