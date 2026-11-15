# Width-42 split and extended domain review

15 November 2026. No mathematical encoding error was found. One inherited scope phrase needs qualification in summaries; it does not affect the actual ID filtering. The frozen `logs/model-review.md` was not changed.

Read all 82 lines of `joint_split.py`, all 58 lines of `run_split.py`, and the complete current `ReplacementCases225.lean` (51 lines), `ReplacementPairs225.lean` (59 lines) and `Simultaneous225.lean` (80 lines). Independently reconstructed the width-39 through width-42 inputs. No solver, compiler or software tests were run; no compiler success or split-run outcome is asserted.

## Domain extension

The audit checked 1106 context records, including every containing-parent list and excluded parent status. It independently reconstructed all 538 noninherited parts: retained vertices, initial masks, terminal degree cores, anchor components, parity counts, crossing totals and rejection/status fields. All 6617 saved peeling steps were valid. Every input pin agreed. No discrepancy was found.

| Width | Contexts | Inherited exclusions | Directly prepared pending contexts |
|---:|---:|---:|---:|
| 39 | 266 | 207 | 59 |
| 40 | 273 | 209 | 64 |
| 41 | 280 | 210 | 70 |
| 42 | 287 | 211 | 76 |

These are preparation counts, distinct from native outcomes. The saved unsplit width-42 result reports 211 inherited exclusions, 69 native infeasibility results and exactly seven unknown IDs, 63–69.

## Exhaustive split

For every ID 63–69, the first interval is $[1,43]$, with anchors 1 and 97 in the lower face. The second intervals are $[c,c+42]$ for $124\le c\le130$, with both anchors in the upper face. The required combined replacement crossing count is two. Each individual count is therefore a nonnegative even integer, so precisely

\[
(k_1,k_2)=(0,2)\quad\text{or}\quad(2,0)
\]

is possible. Running the selected seven contexts with first-crossing arguments zero and two covers the two disjoint possibilities. An unresolved branch remains unresolved; a parent context can be excluded by this split only after both allocations are excluded.

Compared with the previously reviewed solver, `joint_split.py` adds the ID filter and the equality fixing the first part's crossing count. It preserves domains, parity restrictions, the combined crossing equality, cross-part incompatibilities, valid cycle cuts and complete witness reconstruction. The selected IDs are unique and present, so the stored count of seven is correct for the intended command. `run_split.py` changes the executed script and its source pin while retaining the resource/receipt logic. An accepted execution receipt does not by itself assert mathematical infeasibility.

The scope string still contains “All maximal contexts covering blockers7/143”. In this specialized source that phrase must be read as describing the input family, not coverage of the run: only the supplied IDs and one crossing allocation are searched. Final summaries should state this explicitly. The source also correctly states that only the supplied allocation is searched. No edit to the frozen live source was made here.

## Lean statements

`ReplacementCases225.classify` separates an ordered index pair into the eight required positional cases. `ReplacementPairs225` supplies the local, separated, retained/new and fully retained pair deductions. The current `Simultaneous225` constructor combines those local facts without assuming whole-candidate injectivity or inducedness. Its interval-enlargement statement retains the previous containment meaning. No mathematical scope change or new issue was found in these source statements. Their compilation remains a separate obligation, as do the literal model arrays and native contradictions.

## Reviewed hashes

| Artifact | SHA256 |
|---|---|
| `scripts/joint_split.py` | `e8356164a002ed8f32d8710763b16023e1f6ff29ca18974d3e98e01fa7096f74` |
| `scripts/run_split.py` | `dd4ac974a0be544b76ce95569026f2214d9d1e5cb84e5b2670701792b340ab1f` |
| `data/regions39.json` | `f968f412d2035ace9dfba19ca79f04b1ee2faf16b8eafc02dbf452a4cc3b1e4d` |
| `data/regions40.json` | `8fd7bce4939b86cb1198c58e9c7beb8f8592d8844c4e32a42c1234b63f594ccb` |
| `data/regions41.json` | `940edc2e961733464845994d46f004a520034d64b5d280b4a5ef0b42bfe2d6fc` |
| `data/regions42.json` | `b102e8b1c674f378f8437a85790ae6d5b596ec09bf49fc7aab97b6ad2cec2ed9` |
| `lean/ReplacementCases225.lean` | `c4ef95aca7270e7bc7b36a434be78f631dc6696b8a64e108e5ebc18c078bbaf7` |
| `lean/ReplacementPairs225.lean` | `e88a8c6d12037011fd63036d016ffb18ed89035b1e158f3b2860bc084c5fbb5a` |
| `lean/Simultaneous225.lean` | `4980e315fc84bb77d1de69615402875fd105e11858c0d3ad96872640b3a2341e` |
