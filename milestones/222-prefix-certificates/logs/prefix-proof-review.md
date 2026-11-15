# Proper-prefix continuation: accepted proof

Status: `Prefix222` passed Lean on its first guarded compiler run after the parent released the native slot. The run took 2.080 seconds. No repairs or failed compiler attempts occurred. The compiler is terminal and the native slot has been returned to the parent.

`Prefix222.lean` imports only `Std` and introduces no definitions. A path is a function on natural indices with explicit hypotheses restricted to indices at most its edge length `n`: injectivity, allowed-vertex membership, and adjacency exactly for index difference one. Thus the unused function values beyond `n` have no bearing on the result.

`prefix_next` derives all elementary continuation restrictions when `k<n`. The actual next vertex belongs to the allowed set, is adjacent to the current prefix end, differs from every prefix vertex, and has no adjacency in either direction to any earlier prefix vertex. Allowed membership follows from the all-path membership hypothesis; nonrepetition follows from injectivity; the current edge and forbidden chords follow from inducedness and index arithmetic. The hypotheses do not assume that an arbitrary enumerated candidate extends to a full path.

`prefix_nonroot_not_endpoints` uses bounded injectivity alone. If `0<i<=k<n`, equality with either `p 0` or `p n` would force equality of the corresponding indices. This applies in particular to `i=k` when the prefix is nonempty beyond its root. The current last prefix vertex remains internal in the full path because at least one step remains.

`prefix_free_endpoint_zero` expresses the full path's free-endpoint indicator directly as `if p i = p n then 1 else 0` over signed integers and derives its value zero under the same proper-prefix assumptions. It does not take a zero-indicator assumption. For a 93-edge target, substitute `n=93` and retain `k<93`; at `k=93`, the current last vertex is an endpoint and the strict hypothesis is essential.

The source supports coverage by induced next-step candidates and the endpoint-zero rows on proper prefixes. Finite vertex encodings, complete neighbour enumeration, prefix ordering, concrete row serialization and exact numerical certificates remain separate application obligations. These are necessary restrictions; surviving candidates need not have any completion. No numerical bound is asserted.

All three exported theorem reports contain only `propext` and `Quot.sound`. No new axioms, omitted proofs or native decision procedure occur.

## Saved verification evidence

- Source: `lean/Prefix222.lean`, SHA256 `e8913aad9ca17c8614c87157a74ba014e3148f9ea80c4ede9ed2427b32203aea`.
- Receipt: `data/Prefix222-audit.json`, SHA256 `fa3c84224d5fb0965f49070ae35a96c2695868e361b1e1dc0a944612fd1f8228`.
- Accepted object SHA256: `da080af1b1a372285351a1c966e79e4d6426d37a1fb14c5351e5950defa1eb0c`.
- Compiler log: `logs/Prefix222-1794710267981108100/compiler.log`, SHA256 `ed80fc00450747f1de67200a4da69fb89234138057c8316a58371c817d13b5b7`.
- One Lean process ran with `-j1 -s8192`, a 60-second limit, a 256 MiB private-memory limit and a 768 MiB free-memory reserve. Startup free memory was 1,428,180,992 bytes. Recorded samples had at least 1,241,522,176 free bytes and at most 58,273,792 compiler private bytes. These are sampled observations, not continuous peak measurements. All resource checks passed.
- The receipt pins the source, execution plan, checker, native resource helper and accepted `Init` and `Std` dependency objects. No solver or software tests were run for this proof.
