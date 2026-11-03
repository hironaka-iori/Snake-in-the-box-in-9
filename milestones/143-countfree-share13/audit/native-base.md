# Native count-free share13 certificate

Status: `PASS_COMPLETE_NATIVE_RUP_REPLAY`.

The dependency-trimmed certificate has 29,165 deductions, 1,699,457 hints and 10,078 original input clauses. Original clause IDs and literal occurrences are preserved.

This input uses only the ordinary cycle constraints from the base encoding; no added cycle exclusions.

Every trimmed deduction passed an independent ordered unit-propagation replay from the original input clauses, ending in the empty clause. The replay did not call a solver.

One fixed native solver run on the exact prepared input. A complete independent Python RUP replay certifies the finite CNF contradiction only. Lean replay and actual-snake clause interpretation remain pending; no new global bound.
