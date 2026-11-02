# Actual-window transfer for the 012314 outer sum

`lean/SumGeometry112.lean` passed Lean 4.19.0 in 10.984 seconds. The single theorem, `Snake9.SumGeometry112.actual_outer_sum`, uses only `propext`, `Classical.choice`, and `Quot.sound`. It introduces no definitions or types and imports no concrete new contradiction certificate.

For an actual snake $p$ of length $m$, the theorem assumes $r+6\le m$, canonical transition word $(0,1,2,3,1,4)$, and $\alpha_{r+3}\le2$. Its conclusion is

$$
19\le\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}.
$$

The local contradiction remains an explicit argument. Its exact mathematical content is: for all Boolean vertex and endpoint predicates $S,E$, the existing local axioms for

$$
W=(0,1,3,7,15,13,29),\qquad
B=([0,21],[0,21],[0,2],[0,21],[0,21])
$$

are incompatible with

$$
\mathrm{absentCorners}(S,1,0,1)
+\mathrm{absentCorners}(S,3,1,2)
+\mathrm{absentCorners}(S,15,3,1)
+\mathrm{absentCorners}(S,13,1,4)\le18.
$$

The source expresses the window as the existing `winOf [0,1,2,3,1,4]`, and the local centre list as the existing `centresOf` applied to that window and the displayed bounds. No replacement shape, count, or centre definition is introduced. This matches the proposed `Snake9.LocalWindow.Sum3142` semantic interface. Supplying its checked local contradiction will discharge the sole new local premise.

## Reused geometric argument

The proof uses `Guards79.actual_canonical_frame`, the same normalization machinery used by `canonical_interval_exclusion`. Its first-occurrence coordinate list gives an actual coordinate permutation through `mkPerm_spec`. The existing `frame_axioms` theorem then transfers the whole snake's selection and endpoints to the canonical window. The middle interval follows from the explicit middle-count hypothesis; the other four intervals follow from the universal upper bound 21.

The exact count identities are obtained from the already checked `JointTags.frame_count`, imported from milestone 81's copy of the earlier joint-count bridge. The four local centres are precisely:

| Actual path count | Canonical vertex | Incoming direction | Outgoing direction |
|---|---:|---:|---:|
|$\alpha_{r+1}$|1|0|1|
|$\alpha_{r+2}$|3|1|2|
|$\alpha_{r+4}$|15|3|1|
|$\alpha_{r+5}$|13|1|4|

The proof rewrites the four absent-corner counts using these identities and contradicts an outer sum at most 18. It does not infer the sum from the separate centre intervals. The sum contradiction is supplied independently through the local premise.

## Check and scope

The first attempt, run `1793659210799860300`, reached the final count rewrite but failed because `norm_num` left XOR expressions inside the fuel-based logarithms. Its source, checker, log, and failure record are preserved. One source repair replaced that partial simplification by six exact `dirOfStep` identities, checked with `Tags.dirOfStep_eq` and kernel reduction. No native proof shortcut was used.

The second attempt, run `1793659238377485700`, passed. At launch its memory-gate snapshot contained one other Lean process, milestone 104 PID 560, with 2,085,535,744 bytes of private memory. The checker requires at most one other compiler and aggregate private memory below 8 GiB. It used the inherited milestone 111 environment, a separate `build-sum-geometry` directory, and a 120-second timeout. No memory-limit flag was used. The compiler slot is released, and no milestone 104 file or process was altered.

The checker verifies the direct milestone 79 `CanonicalExclusions` and milestone 81 `JointCountBridge` receipts, sources, objects, and logs, plus the exact inherited `LocalWindowTags` object, environment receipts, inspected Tags source, package manifest, and Lean executables. This reuses the audited environment without rebuilding the historical dependency closure. Exact source and checker snapshots accompany both attempts.

The theorem currently covers a forward canonical actual window. It does not add encoded graph filters, reversed-window corollaries, sum-counter semantics, or a concrete refutation. Those are separate integration obligations. No actual-snake sum theorem without the explicit local contradiction, and no new global bound, is claimed by this module alone.

## SHA-256 evidence pins

Paths are relative to milestone 112.

| Artifact | SHA-256 |
|---|---|
|`lean/SumGeometry112.lean`|`012c9b2b8e4e664aa89d1ec4a4832ef23f85b46ea4ec906ea2901856b43d8eba`|
|`build-sum-geometry/SumGeometry112.olean`|`44d0657000229e95d6c554d7cf2ef980bdac4a5162a010d007f4554aaf3040d0`|
|`scripts/check_sum_geometry.py`|`e99a89034d3313aad8fa7fd83107d24b4ee00cbe4ad974c4c373397fe82f828f`|
|`logs/SumGeometry112-1793659238377485700.log`|`e55e144fd67f7a5208310cc7ae1add55c80fad8d065a674658ce6d3d77294d32`|
|`data/SumGeometry112-audit.json`|`385962ab33d07564d97def902a9207421aae9363f60de58c45d80fdfcec5f1e6`|
