# Empty-square shares and window packing

Checkpoint: 21 October 2026. This follows the user's requested empty-square route.
No new unconditional upper bound is claimed.

## Upstream state

The fetched `research/unconditional-241` branch reached
`fcf168386b4797e90a2553d8996b84120bf0294f`. Its three latest commits already
implement the global corner-share inequality, the local share model and its
geometric bridge. This milestone preserves those contributions and develops the
aggregation step. Sixteen relevant files are pinned under `upstream/`, with
original paths and SHA256 hashes in `data/provenance.json`. These are snapshots,
not a wholesale integration of that branch. The collaborator's 237 theorem has
not been independently rebuilt here; main's integrated bound remains 238.

## Checked mathematics

Write e(q) for the number of empty squares through q, d(q) for its selected
neighbors, and s_M(x) = sum over q adjacent to x of floor(M e(q)/d(q)). Set a
zero-denominator contribution to zero. The collaborator's double count is

    sum over selected x of s_M(x) = sum_q d(q) floor(M e(q)/d(q)).

The new **corner-share loss identity** retains the exact discarded quantity:

    sum over selected x of s_M(x) + sum_q (M e(q) mod d(q)) = 4 M s0.

Here n mod 0 = n. The second sum includes both integer rounding and undominated
empty corners. Thus precision changes can be assessed without assuming domination.

The new **weighted window packing lemma** says: if window i has a lower bound
b_i on its share sum, and nonnegative integer weights w_i cover every position
with weight at most C, then sum_i w_i b_i <= C sum_x s_M(x). Clearing a common
denominator gives the rational version. This is a standard double count, with
no claim of historical novelty.

A checked recurrence selects disjoint five-position windows:

    D(0) = 0
    D(n+1) = max(D(n), D(n-4)+b(n-4)) when n+1 >= 5,
             D(n) otherwise.

Then D(n) <= sum_{j<n} s(j). Missing window certificates use b = 0.
The implementation's optimum was compared against exhaustive selection in 240
small instances. The Lean theorem proves soundness of this recurrence; the
computational comparisons separately test the implementation.

At M=12 let G = sum_x (24 alpha(x)+s_12(x)). The upstream theorem gives
G+840v <= 221136. Two new checked conditional consequences specify the target:

- If G >= 114v-191 for every nontrivial snake, then its edge count is at most 230.
- If G >= 114v-1145, then its edge count is at most 231.

The charge-density target is 114/24 = 19/4, with an explicit boundary allowance.
Neither density premise has been proved for all snakes.

## Measured improvement on saved obstructions

Only existing M=12 lower-bound records are used. Unknown values contribute zero;
SAT witness values are never used as lower bounds. The input contains 198 records,
137 distinct five-window bound keys and eight locally excluded keys.

| Saved periodic pattern | Uniform share sum | Packed share sum | Charge mean before | Charge mean after |
|---|---:|---:|---:|---:|
| Eleven positions, alpha mean 42/11 | 1889/5 | 464 | 6929/1320 | 184/33 |
| Six positions, alpha mean 23/6 | 717/5 | 245 | 1159/240 | 797/144 |

For the eleven-position pattern, windows 0..4 and 6..10 give 163+301=464.
For the six-position pattern, one five-position window gives 245. These choices
are independently checked using exact rational arithmetic. One other saved
pattern already contains an upstream model exclusion; two files do not retain
the needed five-centre windows, and are reported as untested here.

These improvements apply to the listed periodic patterns only. They are
conditional on collaborator solver lower bounds. The saved five-window records
omit full selected-vertex assignments and refutation replays; none of those
local numerical bounds is claimed as a new Lean theorem. In particular, the
old 230/231 estimates remain estimates.

## Validation

- Recompiled the pinned upstream ShareCharge module locally; all four printed
  audits use only propext, Classical.choice and Quot.sound.
- Six new theorem audits in `logs/share-packing.log` pass with the same axioms:
  exact loss, weighted packing, recurrence soundness, eleven-position numerical
  packing, and the two conditional global targets.
- All 131 published bank paths independently satisfy their snake conditions,
  the incidence identity, the new exact loss identity, and the M=12 global inequality.
- Two rational packing certificates checked exactly; 240 exhaustive recurrence
  controls passed. Results and hashes are in `data/verification.json`.

Run `scripts/check_lean.ps1` for the Lean checks, then `scripts/packing.py` and
`scripts/verify.py` using the repository's Python runtime and OR-Tools packages.
The script documents the local Lean/mathlib paths. The first Lean run compiles
the pinned ShareCharge source; `-ReuseDependency` is only an incremental option.

## Next proof task

1. Generate and replay the local share refutations supplying the strongest
   useful windows, starting with the 163 and 301 pair and the 245 window.
2. Incorporate the disjoint-window recurrence into a finite-state lower-bound
   proof over every allowed direction/count sequence. Optimizing weights on
   selected cycles alone does not provide that coverage.
3. Track the finite initial/end loss and test the exact 191/1145 allowances above.

This supplements the collaborator's uniform five-window edge weights. It does
not replace their local model, geometric bridge, or certificate obligations.
