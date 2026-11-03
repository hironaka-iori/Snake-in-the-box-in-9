# Milestone 113: pair-count restriction and its limitations

The candidate on canonical directions `012034` is: central counts at most
`(5,4,5)` force the first and fifth counts to sum to at least 9.
The native solver reports UNSAT for a sum at most 8. The concrete
contradiction remains unchecked; two proof-generation attempts timed out.

Lean checks the geometric transfer with that local contradiction as an
explicit premise. A second module checks that the pair deficit can join
the previous maximum-credit argument under `4*a+b<=120`. These two modules
have four printed standard axiom reports and introduce no definitions.

Three independently verified local configurations limit stronger claims.
In particular, exact counts `(6,5,4,5,3)` attain outer sum 9 within the
relaxed model. They are disconnected local configurations with relaxed
boundaries, rather than complete snake constructions.

The pair hypothesis removes 41,361 further graph keys beyond milestone
112, leaving 4,867,866. Both native comparisons retain their earlier
values: completed mean/range 484/557 and conditional mean/range 496/602,
with integer floors 235 and 234. Replacement cycles have zero deficits
under all eight sum rules, so coefficient changes within this fixed
family cannot improve either mean. No new numerical snake bound follows.

Read `mathematical-note.md` for the argument, `data/proof-summary.json`
for evidence levels, and `audit/final-review.md` for the independent checks.
`data/checkpoint.json` and `data/file-manifest.json` freeze this round.

## Reproduction and preservation

- `scripts/probe_sum.py` generates bounded local tests. Existing output
  names are immutable; choose a new milestone for further experiments.
- `scripts/evaluate_intervals.py` and `scripts/evaluate_pair.py` record
  graph comparisons. Existing labels are protected against overwrite.
- `scripts/check_pair_geometry.py` and `scripts/check_budget.py` create
  immutable Lean attempt records and check dependency hashes. They permit
  at most one other Lean compiler and enforce the existing memory gate.
- `scripts/audit.py` reconstructs the failed-proof CNF and checks saved
  evidence. Its output is protected against overwrite.
- `scripts/verify_saved.py --verify` checks the saved manifest and archives;
  `--restore-archives` restores missing large raw files on a fresh checkout.
  Original raw files remain on this machine. Their partial LRAT content
  remains incomplete and is unsuitable for proving the candidate.

Preserve milestone 104's running batch. Its saved observation is a dated
snapshot; verify the current process before resuming any work on it.
The maintained interval remains 191 through 235 edges, with a complete
independent rebuild of the upper-bound evidence pending. Conditional
234 and the exact optimum remain unresolved. Paper revision 106 is
unchanged; the next full revision is 116.

## Next bounded test

On canonical `012310`, test whether the total of the five counts can be
at most 18. Both replacement cycles contain such a window. A valid lower
bound of 19 would remove those cycles, though a full graph calculation
is needed to determine whether replacement cycles preserve the means.
Test both profiles before investing in a concrete proof export.
