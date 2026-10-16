# DFS Lean completion work

Scope: complete and extend the kernel-checked exclusions developed by Steven
Zhan (`stevenreimagined`), preserving the distinction between restricted
regrowth and the global Snake-in-the-Box problem.

## Checked mathematical additions

`work/final_lean/DfsMemo.lean` proves:

- A valid extension remains valid under any replacement ban mask that excludes
  none of its vertices.
- An exclusion can be reused with a larger ban mask and a larger target length.
- An exclusion for a closed reachable region implies the exclusion for the
  original state, provided both closure and coverage of the initial moves are
  proved.
- Such an exclusion implies the original `Snake9.Snake 192` prefix statement.

`work/final_lean/DfsPrefix.lean` defines reversal of an arbitrary induced path
and proves that a 192-edge prefix exclusion also excludes the same prefix and
the corresponding terminal segment in every longer snake. Terminal segments
are read from the final endpoint inward. These are generic implication theorems;
they do not assert that any particular unverified prefix is excluded.

Both additions have compiled under Lean 4.19.0. Their axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound` (some use fewer).

## Certificate status

- The original `DfsCertificate`, `DfsDecide`, `DfsParity`, and bank-data modules
  were rebuilt successfully from the current sources.
- KEEP=144: the complete generated source covers all 262 oriented bank entries.
  Exact duplicate initial states share their literal theorem. There are 21,412
  generated theorems in 721 dependency modules, plus the aggregate. The producer
  reports 1,073,970 cost units, which include leaf-search nodes and bookkeeping;
  this number is not the full C search-tree node count.
- **KEEP=144 verification was paused at the user's request on 16 October 2026.
  169 of 721 dependency modules finished successfully; 2 of 97 aggregate
  dependency targets finished. The aggregate and final axiom audit did not run.
  Generated source alone is not a
  certificate.** The authoritative status and source hashes are recorded by
  `outputs/dfs-lean-144v2/manifest.json`; success requires `PASSED`, a successful
  aggregate build, and a fresh transitive axiom audit.
- KEEP=128, KEEP=120 and KEEP=112 remain uncertified computation results. This
  work does not relabel them as Lean theorems.
- Internal-window uniqueness and the Q8 completion experiments are also not
  certified by a regrowth-prefix theorem.

## Reproduction

Use Lean 4.19.0, Python 3.12 or later, and a C compiler. On Windows the producer
uses `work/snake_dfs.exe`; on other platforms it uses `work/snake_dfs`.

```sh
cc -O3 -o work/snake_dfs work/snake_dfs.c
python work/build_lean_certificates.py --keep 144 --v2 --cap 3500 --split 100
python work/check_lean_certificates.py 144v2 --workers 2
```

The producer rejects incomplete or successful searches when preparing an
exclusion. Search-mode environment variables are cleared explicitly. The Python
runner preserves every build log, returns failure on any failed dependency or
aggregate, checks the final axiom list, and verifies that the source hashes did
not change during the run. Lake can resume already compiled dependencies.

## Cost investigation

The archived KEEP=112 C run reports 5,405,384,421 nodes. An experimental cache
using identical closed reachable regions reduced the first orientation of bank
entry 0 from 73,031,236 nodes to 66,125,655. Retaining stronger numeric bounds
reduced this slightly further to 65,953,111. These probes are not certificates
and do not provide the orders-of-magnitude reduction needed for a practical
direct kernel replay of all KEEP=112 instances.

The general reuse rules above are proved, but a complete producer and checked
certificate using these rules at KEEP=112 has not yet been supplied. No exact
optimum or improved global bound follows from the present work.

## Alternative Boolean certificate route (incomplete)

The new `work/build_regrowth_cnf.py` emits a necessary-condition model for the
suffix graph, with degree constraints, endpoints, parity counts, balanced
threshold counters and square exclusions. Clause provenance and counter
semantics are included. All 262 known 191-edge bank witnesses satisfy their
corresponding positive-control encodings under explicit counter assignments;
see `outputs/regrowth-cnf-positive-controls.json`. This is an executable check,
not a formal proof of the encoding.

For the first KEEP=112 orientation, an experimental encoding of an 82-vertex
suffix was declared UNSAT by CaDiCaL. Its trimmed certificate has 1,547 input
clauses and 5,902 derived clauses. Export to ordinary Lean proof terms produced
150 modules. At the pause, 35 modules had compiled successfully. The final
Boolean contradiction has NOT yet been checked, and a proof connecting these
clauses to every hypothetical snake has NOT yet been constructed. The Boolean
experiment must therefore not be cited as a KEEP=112 exclusion theorem.

The checkpoint archive preserves the experimental encodings, LRAT certificate,
exported Lean modules, partial build caches, logs and explicit paused manifests.
No search or certificate checker remains running after the pause.
