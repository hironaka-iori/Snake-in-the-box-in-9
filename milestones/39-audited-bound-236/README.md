# Audited radius-four bound of 236

This checkpoint incorporates the contributor's completed 236-edge theorem into the rewritten manuscript. The project interval stated in the paper is now **191 <= a(9) <= 236**. The exact optimum remains unresolved.

The source is pinned to [7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/7cb52aad9fbb83aea8a6ced73c9a18a1ad531c9b), on `research/unconditional-241`. Attribution belongs to that contributor development. This integration adds no new global improvement beyond its theorem.

## Evidence and its scope

- The pinned final theorem `Snake9.upper_bound_236` has no window hypotheses. Its companion theorem combines the 191-edge witness with the universal 236-edge bound under the same snake definition.
- The saved Linux audit reports both final theorems depending only on `propext`, `Classical.choice`, and `Quot.sound`. Its replay summary reports all 732 roots completed, 7,190 check modules, and approximately 100 kernel-hours for the reused and new refutations together.
- `upstream/` contains 12 selected source interfaces and receipts, with exact hashes in `data/upstream-manifest.json`. It is deliberately a review snapshot, not a self-contained build of the 39,109-module replay closure. The complete sources, generators, and compressed certificates remain at the immutable upstream commit.
- An independent local enumeration verifies 1,026,432 candidate transitions, including all 611,613 permitted transitions. The table contains 44,064 states and its actual potential range is 0 to 48.
- Four new Lean arithmetic lemmas check the internal boundary constant 291, the endpoint correction 203, the inequality 427m <= 101172, and its integer consequence m <= 236. These lemmas assume the displayed input inequalities; they do not replace the full window proof.
- The contributor's Lean sequence proof uses the valid weaker potential bound 63. The paper now explains why its boundary constant is 294 - 66 + 63 = 291 rather than implying that it came from the sharper range 48.

A clean independent rebuild of the complete 236 proof has not been performed here. The repository's existing local global proof build remains at its earlier checkpoint; the paper cites and incorporates the completed pinned contributor theorem. No generated proof objects are substituted for that distinction.

## Manuscript

The paper preserves the full 238 derivation as an introduction to the method, then proves the 236 refinement using the exact exclusion family, potential step, telescoping sum, endpoint estimates, and square census. The complete 732-row catalogue is saved as JSON and cited as supplementary proof data. Earlier statements and the witness appendix are retained; only the principal interval is strengthened. Authors and hyperlink settings are unchanged.

The existing editor source is synchronized. The built-in compiler still fails before TeX because its Windows restricted-token runner cannot prepare the split writable roots. Source integrity checks therefore do not imply successful typesetting or visual inspection.

## Reproduction

1. Run `scripts/snapshot.py` to retrieve the pinned interfaces and receipts from the local Git object database.
2. Run `scripts/check_potential.py` for the independent finite-table enumeration.
3. Run `scripts/check_arithmetic.ps1` for the four local Lean checks, using the installed Lean and mathlib paths recorded there.
4. Run `scripts/verify.py` to compare snapshot hashes, audit scopes, and manuscript invariants.

`scripts/revise_paper.py` records the one-time manuscript edit and refuses to run again once the 236 theorem is present.

## Research continuation

The new distance-four theorem in milestone 38 remains useful for empty-square accounting. Its low singleton condition forces at least three units of count excess. A global improvement requires coverage of every admitted sequence and one common overlap budget. The current low-mean diagnostic cycle survives the new pair restrictions, so future restrictions should involve intervening counts or additional shapes. The collaborator's work toward 234/235 remains distinct until its complete final theorem and dependency audit are available.
