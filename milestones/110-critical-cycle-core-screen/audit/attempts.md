# Preserved attempts and interpretation

1. All 143 older D roots were screened, without the earlier small-proof
   size filter. Their proposed relaxed boxes miss the two saved limiting
   cycles. This screen creates candidates; it does not prove them.
2. Seven count-conditioned share probes at cap 75 returned native UNSAT.
   Three conditional cases also returned native UNSAT at cap 16. The
   hypothetical seven share floors 76 preserve both numerical comparisons.
3. The no-share control returned native UNSAT on all seven patterns.
   Edge 2139224 required three cycle cuts; the remaining six required none.
   An earlier running summary incorrectly described all seven as having
   zero cuts. The saved JSON files are authoritative.
4. Edge 3534483 was selected for a fresh proof. `certify_plain.py` saved the
   59,251-clause CNF, CaDiCaL LRAT, 1,664-clause core, independent ordered
   RUP replay, and initial generated Lean files. The initial proof has
   2,311 deductions and 217,881 hints.
5. The exact core was solved again with the same CaDiCaL executable using
   `-q --lrat --no-binary --seed=1`, then seeds 2 and 3. Input:
   `work/plain-core.cnf`; outputs: `work/plain-core-sN.raw.lrat` and
   `logs/plain-core-sN.txt`. The input contains exactly the initial core
   IDs, in order. `gen_lean_core.trim_lrat` retained the dependencies of
   the empty clause in `work/plain-core-sN.trim.lrat`. All three seeds
   produced the same 2,007 deductions, 177,364 hints and 1,172 used
   original core clauses. The exported core retains all 1,664 clauses.
6. `prepare_lean.py` uses seed 1, maps core IDs back to full-CNF IDs, and
   renumbers the 1,069 active variables first. It updates every variable
   meaning and counter literal consistently. Lean rechecks all semantics;
   the independent audit also replays the renumbered proof. This permits
   use of the already audited 2,400-offset checker. No historical checker
   or compiled support object was changed.
7. The first attempt to run `evaluate_count_rules.py --all` stopped at its
   assertion requiring zero extra cycle cuts. No all-cases result was
   written. `evaluate_count_rules_all.py` additionally checks that every
   saved cycle-cut vertex set has minimum induced degree at least two.
   Its graph result remains hypothetical, since those six further
   exclusions have no checked contradiction yet. The successful one-case
   experiment retains the original evaluator's exact hash.
8. All 64 isolated proof modules and the actual-snake application passed.
   Six printed axiom reports are audited; only the standard permitted
   axioms occur. The exact logs, objects' hashes and source snapshots are
   recorded. The source manuscript was not changed in this round.
