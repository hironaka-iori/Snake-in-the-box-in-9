# Milestone 79: encoded exclusion guards

This continuation proves how the finite graph's count filters apply to actual
snakes. It preserves the maintained interval of 191 through 235 edges. The
proposed 234 bound remains conditional on the outstanding local shares, full
graph interpretation and potential replay.

## Checked statements

The six Lean modules have 31 printed theorem audits. The canonical-window
interface applies a local refutation to any actual snake window, in either
orientation. Count slices are identified exactly with the graph's base-six
integer operations. Encoding is injective for fixed-length lists of symbols
from one through six.

For a nine-direction window beginning at r, the represented counts occur at
r+3 through r+8. A width-w filter at offset s examines counts r+s+3 through
r+s+w+2 and directions beginning at r+s+2. Here 2 <= w <= 6 and s+w <= 6.
The extracted count code is

\[
\left\lfloor c/6^{6-s-w}\right\rfloor\bmod 6^w.
\]

All these count positions are strictly internal when r+9 <= m. The saturation
lemma transfers an interval test on min(6,a) to one on a whenever a <= 21,
the lower endpoint is at most six, and the upper endpoint is below six or is
21. In particular, symbol six retains its full meaning [6,21].

`IntervalCatalogue.lean` instantiates the ten completed milestone-72 local
refutations. Every actual snake survives these ten interval filters at all
three applicable offsets and in both orientations. These results have no
unproved catalogue premise. Their existing certificate objects are reused;
this round does not replay their entire dependency closure.

The reference-catalogue interfaces remain conditional on the supplied local
refutation. The source audit identifies 1,378 canonical reference keys and
2,678 distinct oriented pairs, obtained from the 235 and 236 catalogues. Their
closed contributor proofs have saved upstream audits, but their full union
has not been imported and assembled in this environment.

## Evidence and reproduction

- `data/proof-summary.json` pins the six successful module receipts.
- `data/interval-support.json` pins 2,131 existing source-matched certificate
  objects and their sources. This distinguishes reuse from a new clean build.
- `data/filter-comparison.json` records 279,936 digit comparisons, 699,840
  slice comparisons and 2,799,360 interval-guard comparisons over all 46,656
  six-count codes. This finite Python comparison is separate from the Lean
  proof and does not encode the Python interpreter in Lean.
- `audit/reference-catalogue.md` records the exact catalogue provenance and
  import gap; `audit/guard-review.md` independently reviews indexing and
  hypotheses.
- `data/checkpoint.json` and its frozen replay records record case7305's
  status at the time of capture. Inspect the live process before restarting.

Use the existing Lean4.19.0 environment and checked milestone78 support.
Run `scripts/check.py` on CanonicalExclusions, CountWindows, BaseSix,
ReferenceRetention and IntervalGuards in dependency order. The first three
are independent after CanonicalExclusions, except that CountWindows imports
it. Run `scripts/prepare_intervals.py` to pin the completed milestone72 objects
and generate IntervalCatalogue, then check IntervalCatalogue. Run
`audit/check_filters.py` for the finite convention comparison. All commands
are relative to this milestone and use the repository's saved Python runtime.

## Remaining work

The full retained-edge theorem still needs the reference catalogue, the
forty recovered short rules, the three history exclusions, and an exact
retained-array lookup. The ten interval filters are now connected to actual
snake counts. Credit validity, all compatible eleven-direction realizations,
the full potential and remaining count-free share targets remain separate
obligations. None of these interface checks establishes 234 or the exact
optimum.

The paper remains revision76. Authors, hyperlink settings and both manuscript
copies are unchanged. The next scheduled full paper revision is round86.
