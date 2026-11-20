# Long-term goal for the nine-dimensional snake

Determine the maximum number of edges in a snake in the nine-dimensional hypercube. Seek longer snakes and verify each construction. Use the structure of lower-dimensional snakes to prove which constructions can succeed and which are impossible. Work toward an explicit snake and a proof that every longer snake is impossible. Draw on collaborators’ verified upper bounds and state precisely which cases each result covers.

## How to continue the research

Follow the marked construction route across rounds. Use the current handoff to resume from verified work. Keep alternative approaches in the route index and consult `thoughts.txt` for suggestions. Treat proposed numerical values as conjectures until proved. [Marked route](ACTIVE.md) · [Current handoff](../../handoff/CURRENT_STATUS.md) · [Alternative routes](README.md)

Codex chooses its own round objectives and keeps the next experiment in the local route notes. The long-term goal carries across rounds. Report completed results and their scope at each pause.

## What counts as evidence

For a longer snake, save its ordered vertices or transitions and verify the dimension, distinctness, adjacency of consecutive vertices and absence of any nonconsecutive adjacent pair. For an exclusion, specify the full family, reconstruct the search constraints, cover every case and check the certificates. Record unfinished branches explicitly. Distinguish written proofs, Lean statements, checked finite computations and conjectures. Use the primary literature when assessing novelty. Global upper-bound work belongs to collaborators. Review their published proof status before citing it.

## How to finish a round

Save the question, reasoning, inputs, results and verification records in the round's milestone folder. Update the marked route and handoff. When the research frontier changes, update both manuscripts in `D:/Codex/2026-10-13/new-chat/outputs`, keep exact mirrors under `E:/Snake-in-a-box/paper`, and compile both. Preserve Iori Hironaka, Tommy Ma and Steven Zhan as authors and retain the existing hyperlink settings. Keep the ten-round review of the full written sources.

Run one heavy search or compiler at a time. Require at least 1 GiB of free memory to start, retain a 768 MiB reserve, and enforce the 256 MiB private-memory limit. Use one Lean thread and at most 60 seconds per module. Software tests require an explicit request. Mathematical certificate checks and Lean compilation are part of the research.

Commit only the round's work, push it to GitHub and verify the published revision. Honour the latest requested round count or pause. When a pause is due, save the resumption point locally and pause the goal after publication. A verified improvement over the best known construction merits a pause for review.
