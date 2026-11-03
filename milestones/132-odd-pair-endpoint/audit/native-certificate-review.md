# Native endpoint-query certificate

Status: `PASS_COMPLETE_NATIVE_RUP_REPLAY`.

The dependency-trimmed certificate has 13,299 deductions, 554,859 hints and 683 original input clauses. Original clause IDs and literal occurrences are preserved.

Used positive endpoint-parity clauses: []. Used negative common-sphere endpoint units, by vertex: [0, 10, 18, 34, 66, 130, 258]. Exact original IDs are recorded in `work/certificate/core-premises.json`. These dependencies are specific to this certificate and are not asserted minimal.

Every trimmed deduction passed an independent ordered unit-propagation replay from the original input clauses, ending in the empty clause. The replay did not call a solver.

One fixed native solver run on the exact prepared input. A complete independent Python RUP replay certifies the finite CNF contradiction only. Lean replay and actual-snake clause interpretation remain pending; no new global bound.
