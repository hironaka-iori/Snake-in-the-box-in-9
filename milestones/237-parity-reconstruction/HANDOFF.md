# Current state after round 237

The goal is ACTIVE. Complete publication of round 237, continue with full rounds 238 and 239, and pause after round 239. The earlier interruption in milestones/237-parity-reconstruction/PAUSED.md is historical and superseded by the resumption. Work in E:/Snake-in-a-box. Read the current mathematical note and source-bound receipts before continuing.

The maintained interval is \(191\le a(9)\le231\). The contributor theorem at revision 478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088 has a successful saved final assembly and standard-axiom audit in milestones/36-lean435-port/audit231. Its source states the universal 231-edge conclusion without a remaining certificate or share-floor premise. A fresh independent rebuild of the entire contributor proof remains pending. No longer snake or new global bound was obtained in this construction round. The conjecture \(a(9)=196\) is unresolved. Coworkers handle upper bounds; continue construction and structural work.

## Majority exchange and its evidence

A 192-edge snake has 193 vertices, split into majority and minority classes of sizes 97 and 96. For each of the 145 saved 96-vertex parity sets, this round considers removing one old vertex and inserting two different same-parity vertices. The opposite class, ordering and endpoints remain free. These are 177,062,400 descriptions before deduplication.

The contraction graph joins two selected majority vertices when some opposite-parity vertex has exactly those two selected neighbours. Parallel labels count once. A snake with that majority set exists exactly when the simple contraction graph has a Hamiltonian path. The mathematical equivalence is explained in MATHEMATICAL_NOTE.md and spectral/BRIDGE_REVIEW.md.

Deleting r positions from a Hamiltonian order leaves at most r+1 runs. Consequently every partial selection satisfies \(2I+L\le2r+2\), where I counts isolated vertices and L counts leaves in its contraction graph. For a completed selection U and arbitrary subsets S,T, the necessary directed-cut inequality is

\[
2|S|\le2|T|+2+e(S,U\setminus T).
\]

The last term counts distinct ordered graph edges. The two endpoint deficits account for the additive 2; each destination in T receives at most two path incidences. Overlap between S and T is allowed.

Two archived independent enumerations agree on 679 surviving descriptions, representing 623 distinct sets. Every set has an explicit violated cut. The current finite-input audit reconstructs all 679 descriptions, all 623 contraction graphs, their cuts, their original Lean declaration inputs, and all 145 archived necessary-degree models. The full enumeration and solver executions were not rerun. The independent executable's archived binary digest was not revalidated against a located executable; its source and saved output remain available.

All 623 literal numerical cut inequalities now have accepted Lean receipts, compiled in 125 sequential modules of at most five statements. The path-index inequality, partial-deficit statements, and geometric helper lemmas have separate accepted receipts. Their complete proof-assistant assembly remains open: the escapes computation still needs its distinct-target counting identity and reindexing to the actual path positions. Thus the numerical cut checks alone do not establish a complete Lean saved-family exclusion. The written bridge is recorded in spectral/BRIDGE_REVIEW.md.

A separate necessary-degree model reports INFEASIBLE for every one of the 145 families, before connectivity cuts. All unselected degrees are unrestricted. Its constraints and selection guards were independently reconstructed. These native contradictions have no Lean replay. The archived circuit results exclude the same 623 final graphs and retain the same solver-evidence limitation.

Combining these covers with the preceding ones gives majority overlap at most 94 and minority overlap at most 92. Under the recorded finite/native evidence, any 192-edge snake shares at most 186 vertices with each saved 191-edge seed or cube-isometric copy. It must omit at least six old vertices and introduce at least seven new ones. This is a proximity restriction relative to the saved collection; it gives no global upper bound.

## Actual-cube reconstruction

The complete recursive Q9 inverse and its two-missing-count theorem passed the guarded Lean rebuild. Sixteen 32-case coefficient modules replace the memory-exceeding monolithic calculation without changing the statement. The inverse weights are 35, -10, 8, -16 and 128 at distances 1, 3, 5, 7 and 9, with factor 315.

Neighbour counts at any 510 of the 512 vertices determine a binary vertex selection uniquely. The proof applies the inverse at the antipodes of the two missing positions and eliminates the resulting integer equations. This is a theorem about arbitrary binary selections, with no snake or symmetry assumption. For a selection confined to one parity side, the counts on that side are zero automatically; any 254 of the 256 opposite-side counts therefore suffice. This last statement is a written specialization of the checked theorem.

Counts at retained snake vertices leave many other counts unspecified. Never replace these unknown counts by zero. Reconstruction does not itself guarantee connectivity or supply a longer snake.

## Continuation and frozen search states

At exactly four minority replacements, class 139 remains INFEASIBLE. Classes 7, 6 and 0 remain UNKNOWN after their recorded 40-second runs; 141 classes remain unqueried. The current majority result changes none of these statuses. The next open majority family removes two old vertices and inserts three, giving overlap 94. Neither that family nor the complete four-replacement minority family is excluded.

Continue a single construction route at a time. A useful next approach is to combine the retained-neighbour balance equations with the new majority and minority overlap restrictions. A proposed majority change forces removal of every old internal minority vertex whose added and removed neighbour counts differ; the old minority endpoint has its separate one-extra-addition condition. Use these necessary conditions to select candidates before ordering them. Full neighbour-count consistency can constrain unknown counts once they are represented explicitly. This proposed generator has no established performance improvement. Partial greedy growth remains an optional local method.

Preserve the round-235 two-replacement cover, round-234 one-replacement cover, round-233 saved-parent deletion ceilings 46/92/186, round-230 two-block exclusions, round-222 one-crossing ceiling, and all frozen historical outcomes in the prior completion records. Round 193 already closes repeated length-preserving contiguous replacements of at most 33 edges within the saved bank. Ordinary square reroutings are included in that closure.

## Evidence and publication discipline

The main evidence is in milestones/237-parity-reconstruction:

- MATHEMATICAL_NOTE.md: written argument and limitations.
- data/finite-input-audit.json: reconstruction of saved finite inputs, native models and numerical cuts.
- majority/kernel-cuts.json: all 623 accepted literal cut inequalities.
- data/inverse-replay.json: actual-cube inverse and two-erasure proof.
- data/spectral-replay.json and data/axis-replay.json: path criteria and geometric helpers.
- data/example-replay.json: checked supporting finite example.
- spectral/BRIDGE_REVIEW.md: complete written bridge and remaining Lean obligations.
- logs/: retained failed and successful source-bound compilation records.

The authoritative manuscripts are D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and snake9_frontier_explanation.tex, with exact paper/ mirrors. Preserve all three authors and the original hypersetup. Both updated manuscripts compiled successfully with the desktop compiler; their saved receipts and exact mirror hashes are in data/completion.json. The publication manifest records the checkpoint files. The full-source review last occurred at round 230 and is due at round 240.

Use one heavy worker/compiler at a time. Retain the existing resource limits: at least 1 GiB startup free memory, 768 MiB reserve, 256 MiB private-memory ceiling, one native thread, and Lean with 60 seconds, -j1 and -s8192. Preserve failed logs and exact dependency hashes. Keep publication narrow and Git pack memory bounded. Preserve the unrelated .gitignore and milestone-50 tracked edits. The root worker owns completion.json, final compilation, commit and push. Do not pause at round 237; continue through round 239 unless the user changes the instruction.
