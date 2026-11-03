# Continuation assignment

Continue the empty-square/count-sum route in `E:/Snake-in-a-box`, using
existing notation. Read milestone 114's mathematical note, proof summary,
checkpoint and final review. Keep the research goal active. Verify the
live milestone 104 process before changing anything associated with it.

## First proof task

Reduce the cost of the selected native contradiction and check the
concrete five-count inequality in Lean. The target is canonical `012310`,
five internal count total at least 19, with no additional count caps.

Selected evidence in milestone 114:

- `data/012310-total18-certificate.json`.
- `work/012310-total18/full.cnf`: 3,129 variables, 55,860 clauses,
  including eight connected induced-cycle exclusions.
- `work/012310-total18/full.trim.lrat`: 5,206 used original clauses,
  358,464 deductions, 22,088,504 hints; independently replayed after
  mapping identifiers back to the full formula.
- `work/extracted-core-scratch/core.trim.lrat`: the same selected
  deduction before full-CNF identifier mapping.
- `scripts/replay_core.py`: successful two-stage RUP replay.

Do not reclassify this as a checked actual-snake theorem yet. The full
Lean certificate and its concrete interpretation remain pending.
`TotalGeometry114.actual_total_sum` checks only the geometric transfer
under an explicit local contradiction. `Comparison114` checks three
arithmetic statements; neither module discharges the concrete contradiction.

The existing core-refinement/export scripts in milestone 112 are useful
references. Try a bounded refinement or changed solver configuration
before exporting hundreds of thousands of deductions. Preserve the
selected verified certificate if another attempt fails or grows.
Use system temporary storage for large native proof output, followed by
a verified copy to the research folder. The unchanged formula/options
completed there in 20.656 seconds after a 60-second attempt on the research
volume timed out; their first 40,935,424 proof bytes are identical.

The first extracted-core attempt failed because its literal order differed
from the original clauses. Independent multiset matching found 4,535 such
permutations among 5,431 extracted clauses. The successful attempt restores
the original literal order. Preserve both input mappings and all failed
attempts. The separate DRAT conversion timed out and its LRAT is partial;
the successful selected contradiction comes from the later direct LRAT run.

The 115-cycle strengthened alternative retains 29,534,822 hints and is
unselected and unreplayed. Do not silently use it in place of the verified
22,088,504-hint certificate. All its cycles were independently checked as
valid exclusions, but that alone does not check its proof.

## Lean export requirements

The five-count sum contains 105 literal occurrences and 84 distinct
literals: 68 occur once, 11 twice and 5 three times. Deduplication changes
the inequality. Reuse `SumCountSemantics112` with all five selected centres.
The window vertices are `[0,1,3,7,15,13,12]`, and the centre/direction pairs
are `(1,0,1),(3,1,2),(7,2,3),(15,3,1),(13,1,0)`.

When adapting the milestone 112 exporter, append this case's cycle cuts
before asserting equality with the saved full CNF and generating tags.
Its earlier proof had no such added cuts. Keep the extra sum counter and
its full multiset of negative primary literals. Check every finite
counter/tag/permutation claim in Lean before combining with the refutation.

Count active variables before choosing an audited checker offset and
word width. The previous 112 proof used a bijective renumbering to put
1,718 active variables below offset 2,400. This case may need a different
audited variant. Preserve the full variable bijection and independently
check its CNF, proof and meaning-table transformations.

Use at most one additional Lean compiler alongside milestone 104, with
the existing memory gate. Preserve unique failed attempts and all hashes.
Do not count generated modules as checked. The eventual actual-snake
theorem must discharge `hlocal` without a collective reference-catalogue
premise and print its axiom dependencies.

## Mathematical comparisons and subsequent target

The total-19 finite experiment retains 4,865,603 full keys, 2,263 fewer
than milestone 113. Its completed-floor mean/range is `2424/5,2881/5`,
with comparison `5517073/23424` and integer floor 235. The conditional
profile remains mean/range `496,602`, comparison `551765/2348`, floor 234.
Both assume the earlier unproved sum rules.

The total-20 hypothesis has only an UNKNOWN 30-second probe. It retains
4,859,836 keys and lowers the first range to 565, with comparison
`5517017/23424`; both integer floors remain unchanged. It supplies no
UNSAT support for the stronger local bound. Saved zero-deficit cycles
bound the means by `2424/5` and 496 for all nonnegative coefficient choices
within these fixed families. Do not repeat coefficient sweeps.

Lean checks that excluding 235 via the existing comparison requires
`227*p > 111960*d+R`; excluding 234 requires `226*p > 116160*d+R`.
At mean at most `2424/5`, every nonnegative potential range still permits
235. More range optimization alone cannot reach 234 from this mean.

After advancing the concrete proof, test the common surviving suffix
shape `012345`. Exact count tuples are `(4,3,3,5,4)` for the completed
cycle, and `(5,4,2,5,5)` or `(5,4,3,4,5)` for the stronger hypothetical
conditional cycle. The broad middle count at most 3 and total at most 21 cell is
untested. Verify any local witness directly, and compare viable
restrictions on both full profiles before expensive proof export.

## Preservation

The old milestone 104 attempt ended with a termination code and no Lean
diagnostic. Its unchanged retry passed in 175.61 seconds, and the original
batch driver resumed. Saved observations are dated; query the live process.
Do not restart a live job or alter its sources. Retain failed and successful
receipts, including the stopped-state snapshot in114.

Use `scripts/verify_saved.py --verify` for this round. Missing large raw
proof files can be restored with `--restore-archives`; they remain present
on this machine. The live resumed-batch output logs are deliberately outside
the frozen manifest; immutable snapshots are saved instead.

The original reference union still has 1,366 unresolved entries; checked
indices are `0,472,495,535,572,602,619,620,1006,1010,1011,1014`. Complete
global integration and the maintained upper bound's independent rebuild
remain pending. The range is 191 through 235 edges; conditional 234, the
optimum and 196 remain unresolved. Check GitHub and publish reviewed rounds.
Keep the three authors and hypersetup. Paper revision 106 remains current;
perform the next full revision at 116. Introduce no unnecessary definitions.
