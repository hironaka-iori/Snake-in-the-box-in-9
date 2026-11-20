# Continuing goal for the nine-dimensional snake

Find and verify an induced path of at least 192 edges in the nine-dimensional cube. If a construction family cannot reach 192, prove the strongest justified statement about that family and use it to choose the next candidate. Treat 196 as a conjecture. A restricted upper bound leaves the global maximum open.

## Where to start

1. Read the [marked route](ACTIVE.md) and [current handoff](../../handoff/CURRENT_STATUS.md). Check the latest milestone, local changes and published branch before choosing the next round number. Start at the first unresolved case in the marked route.
2. Follow single-crossing joins of two eight-dimensional paths across successive rounds. Use the 98-edge optimum and shorter parents to compare endpoint choices, parity, coordinate symmetry and which projected vertices a partner must avoid. Keep alternative approaches in the [route index](README.md). The local working note `thoughts.txt` is a source of suggestions.
3. If all recorded parents close, generate new parent shapes on this route, compare them up to cube isometry and reversal, and retain explicit representatives. Record both choices of joining endpoint unless an explicit symmetry identifies them.

## What counts as evidence

For a longer snake, save its ordered vertices or transitions and verify the dimension, distinctness, adjacency of consecutive vertices and absence of any nonconsecutive adjacent pair. For an exclusion, specify the full family, reconstruct the search constraints, cover every case and check the certificates. Record unfinished branches explicitly. Distinguish written proofs, Lean statements, checked finite computations and conjectures. Use the primary literature when assessing novelty. Global upper-bound work belongs to collaborators. Review their published proof status before citing it.

## How to finish a round

Save the question, reasoning, inputs, results, verification records and next case in the round's milestone folder. Update the marked route and handoff. When the research frontier changes, update both manuscripts in `D:/Codex/2026-10-13/new-chat/outputs`, keep exact mirrors under `E:/Snake-in-a-box/paper`, and compile both. Preserve Iori Hironaka, Tommy Ma and Steven Zhan as authors and retain the existing hyperlink settings. The Round 250 review covers the full written sources.

Run one heavy search or compiler at a time. Require at least 1 GiB of free memory to start, retain a 768 MiB reserve, and enforce the 256 MiB private-memory limit. Use one Lean thread and at most 60 seconds per module. Software tests require an explicit request. Mathematical certificate checks and Lean compilation are part of the research.

Commit only the round's work, push it to GitHub and verify the published revision. Honour the latest requested round count or pause. When a pause is due, record the precise resumption point and pause the goal after publication. A verified improvement beyond 191 merits a pause for review.
