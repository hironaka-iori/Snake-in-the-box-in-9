# Execution and verification scope

The actual counterexample Lean check passed on its first compiler attempt in
36.656 seconds, with nine standard axiom reports. The saved compiler gate
inventory was refreshed before launch. Neither existing batch was restarted.

The separate plain-encoding audit initially stopped before producing a result
because the shared solver-package directory was missing from its import path.
After that correction it stopped before encoding because the plain encoder
requires tuple bounds. The final script adds the existing package directory
and converts the same JSON bound pairs to tuples. Both full formulas then
matched the original bytes and both saved proofs passed the separate replay.
No earlier failed audit was reported as a pass, and no solver evidence changed.

The generic evaluator copied at the start was not run. The executed
`evaluate_oriented.py` explicitly reverses count tuples for asymmetric bounds
and checks the entire previous removal set and both previous weight hashes.
The independent graph audit checks saved cycles, 2180 orientation examples,
potential bytes and arithmetic; it does not rerun every edge inequality.
The producer performs the full edge checks. Negative Lean theorems remain pending.
