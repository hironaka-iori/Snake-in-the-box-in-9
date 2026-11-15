# Closed-cycle parity inequality: accepted proof

Status: `CutParity221` passed Lean on its first compiler attempt after the native slot was released. The guarded run took 3.108 seconds. Both exported theorem reports were accepted; no repairs or failed compiler attempts occurred. The compiler is terminal and the slot was returned to the parent.

The source imports only `Std`. Its sole definition, `changes start tail`, lists adjacent Boolean disagreements along a walk. Applying it to `rest ++ [start]` includes the closing edge and fixes closure explicitly. No assumed even-parity premise replaces this closure.

The proof has two steps. Induction on a walk proves that its disagreement count is even when the endpoints agree and odd when they differ. Specializing the endpoints gives `closed_cycle_even`. For an equally long Boolean marked-edge pattern, the signed disagreement sum equals the number of marked edges minus the number of positions where the marked pattern and disagreement pattern differ. Zero mismatches force the two lists equal. An odd marked-edge count cannot equal the even closed-walk disagreement count, so at least one mismatch occurs. This gives `odd_cycle_inequality` over signed integers.

If the marked edges are a subset F of a cycle C, the conclusion is

\[
\sum_{e\in F}\delta_e-\sum_{e\in E(C)\setminus F}\delta_e\le |F|-1.
\]

The theorem permits arbitrary closed Boolean walks, including repeated labels; a simple graph cycle is a direct specialization. It requires that the marking list has exactly one entry per edge and an odd number of true entries. It has no hypothesis asserting the desired inequality or even disagreement parity.

The correspondence between edge disagreements and `x_a+x_b-2y_ab` for Boolean selections with induced-edge products is already checked in `SquareParity220.boolean_disagreement`. This new source does not import or alter that module. Concrete cycle enumeration, edge order, marked subsets and integer/rational array interpretation remain application obligations. No numerical bound or native search conclusion is asserted.

`closed_cycle_even` reports only `propext` and `Quot.sound`; `odd_cycle_inequality` additionally reports `Classical.choice`. No new axioms, omitted proofs or native decision procedure occur.

## Saved evidence

- Source: `lean/CutParity221.lean`, SHA256 `24f789fd4c9f293925c190debe679ba4e535948c01bb664e061ac2a3cde37912`.
- Receipt: `data/CutParity221-audit.json`, SHA256 `646a74bc6c58db9579e2dca092e2960b4923e7bb72b2d9e27d6ee9dc8e4d3483`.
- Accepted object SHA256: `062be3bbbec8002589f784760847be6c28d3db8e151a2b8a7696b9820eb373de`.
- Compiler log: `logs/CutParity221-1794709372270127600/compiler.log`, SHA256 `9c63f74966de2483828ce8b82a9ed2fed8fe89cd91b657582d757ccb22660211`.
- The execution used one Lean process, `-j1 -s8192`, a 60-second limit, a 256 MiB private-memory cap and a 768 MiB free-memory reserve. Startup free memory was 1,884,749,824 bytes. Recorded samples had at least 1,649,823,744 free bytes and at most 118,472,704 compiler private bytes. These are sampled resource observations, not continuous peak measurements.
- The receipt pins source, execution plan, checker, native resource helper and the `Init` and `Std` dependency objects. No solver or software tests were run for this proof.
