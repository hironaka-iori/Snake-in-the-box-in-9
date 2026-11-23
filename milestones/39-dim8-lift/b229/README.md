# B229 stuck hard cubes: one-level manual split study

The eight k = 31/32 cubes on which the tail route's vertex splitting built no leaf (L = 116):
6996966996696996, 1669966996966996, 1669699696699669 (pilot), 1669966996696996, 0778788778878778,
1669699669969669, 1669699696696996, 1EE1E11EE11E1EE1.

Per cube (`run_cube.sh HEX K SKIP_PARENT`):

1. **Parent** F ∧ C: `lean --run Export.lean 13 116 <hex> <k> parent.cnf q` (`cubeCnfQ`). C is the first
   64 lines (`famFix A`, unit clauses fixing the copy-0 selection variables sV(u) = u + 1, u < 64); F is the rest.
   `cubes/<hex>/hashes.txt` has sha256 of parent.cnf, C.units, F.body and the DIMACS header.
2. **Unit propagation** (`up.c`, two watched literals) on the parent; no parent conflicts.
3. **Candidates**: the 16 free outer selection variables sV(u), u = 64..255 (DIMACS 65..256), with the most
   occurrences in remaining clauses of free length 2-3. For each, propagation after +x and after -x
   (`probe16.jsonl`: conflict, assigned, remaining clauses / vars / binaries / ternaries).
4. **Children**: for the top 4 (no side closes by propagation, so ranked by the harder side's remaining
   clauses) `mkchild.py` writes F ∧ C ∧ x and F ∧ C ∧ ¬x: the parent's bytes plus one unit clause, header
   clause count + 1, same variable count; verified byte-for-byte before solving (`children.jsonl`: sha256,
   write time, on-disk time).
5. **Short solves**: CaDiCaL 2.1.3 `--unsat --lrat --binary=false -t 45` on both sides of each cut, and on
   the parent (skipped for 6996966996696996 and 1669966996966996, whose unsplit solves run elsewhere);
   wall time and peak RSS per run (`meas.py`, `timing.jsonl`), solver logs `cubes/<hex>/*.log`.

Result (`summary8.txt`): on all eight cubes no candidate closes a side by propagation (+x fixes ~1.8 k more
variables, -x ~0.3-0.8 k, against 67-74 k at the parent), and every child and parent solve is UNKNOWN at
45 s, with conflict counts at the parent's level. No first cut shows a gain at this budget, so no second
level was tried; all eight are "split undecided, whole cube first". The child CNFs and partial proofs stay on
the study machine (`/home/user/b229/<hex>/child`, 14 MB each); they are reproducible from the hashes here.
