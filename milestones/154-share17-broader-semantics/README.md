# Broader share-17 clause semantics

Status: all 98 modules passed Lean. The complete contradiction remains pending. Read MATHEMATICAL_NOTE.md and data/semantics-completion.json.

The target is the existing five-centre share bound for direction pattern
`012032`, with weaker count conditions than the exact-context certificate:

\[
\alpha_{r+1}=4,\qquad \alpha_{r+2}\le 4,\qquad
\alpha_{r+3}=4,\qquad \alpha_{r+4}\le 5,\qquad
\alpha_{r+5}=3
\quad\Longrightarrow\quad
17\le\sum_{i=0}^{4}\operatorname{coreShare}_{12}(p,r+i+1).
\]

The source also treats reversed canonical directions. In the original path
order, that case requires counts `3, at most 5, 4, at most 4, 4`.

The broadening removes two lower bounds whose counter registers do not occur
in the retained contradiction. Milestone153 has already replayed the renamed
numerical contradiction and checked that its compact CNF is unchanged. This
milestone prepares a new interpretation of that same CNF using nine counters.
It does not modify the exact-context files or generate another contradiction.

## Files and order

- `scripts/prepare.py` reproduces the broader encoding, checks its saved tables
  and compact clause identity, and writes the source inventory.
- `lean/Share154/Data.lean` contains the broader bounds, regenerated counter
  indices, literal meanings, and tags. It imports the original
  `LocalWindowCnf.ShareWindow153` module.
- `lean/Share154/Structure.lean` and `lean/Share154/Shard00.lean` through
  `Shard92.lean` prepare counter/totalizer and individual clause checks.
- `lean/Share154/Semantics154.lean` prepares the implication from an
  unsatisfiable shared CNF to the broader local share bound.
- `lean/CriticalShareAdapter154.lean` prepares transport to actual snakes,
  including coordinate renaming and reversal of the five count intervals.
- `data/source-plan.json` pins 97 new source modules and all generator inputs.

The existing shared CNF module must be checked as an external dependency.
The existing generic framework and canonical adapter must resolve to their
intended previously checked versions. The exact-context semantic modules are
not dependencies of the broader interpretation.

## Remaining checks

1. The shared CNF module and all 97 new source modules passed Lean.
2. Check the milestone153 replay pilot, then the complete single contradiction
   against the shared CNF. Do not infer completion from the numerical replay.
3. Compose the checked contradiction with the broader actual-snake theorem.
4. Recompute and check the global potential before asserting a stronger global
   upper bound. This milestone supplies no new global bound.

The prepared actual-snake theorem retains an explicit `Unsat` premise until
step 3. The implication is checked; the share-17 bound under only the stated counts remains pending.
