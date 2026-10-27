# Milestone 56: zero-credit packing limitation and paper revision

The selected route remains **empty-square charging**. The mathematical and manuscript-source checks pass: two Lean modules, ten dependency audits, and independent checks of the graph cycle and all thirteen printed snake witnesses. The contributor-checked interval remains **191 <= a(9) <= 235**. The complete contributor dependency closure has not been independently rebuilt locally.

This is research round 10 of 10 after manuscript revision 46. The scheduled revision is saved in `paper/snake9_research.tex` and synchronized with the existing editor source. The next scheduled revision is after ten further rounds, at milestone 66.

## Mathematical finding

Before constructing a larger state space for exact interval packing, the replacement cycle from milestone 55 was checked for a decisive limitation. It has 25 transitions, appended truncated-count sum 102, and zero recorded share credit on every transition.

Summing a potential inequality around this cycle cancels the potential. Thus a count-normalized lower mean cannot exceed 102/25 while this cycle remains admitted and receives only the existing zero credits. Every selection or nonnegative weighting of those credits still sums to zero. Even with zero potential loss, this ceiling cannot exclude 235 through the present charge accounting.

Lean checks the count sum, general telescoping implication, zero-credit packing identity, and the arithmetic limitation. An independent verifier identifies each saved transition in the actual graph arrays and checks the array hashes against the preceding model archive. The claim concerns the finite relaxation and the recorded lower bounds. It does not assert that the cycle extends to a complete snake or that the actual empty-square shares vanish.

This result rules out spending the next round merely optimizing the packing of the same catalogue. The useful next step is to extract the entire replacement minimum-charge family and seek a new share inequality that applies to it, using ordinary feasibility as a control. A valid additional restriction on its transitions could also remove the obstruction, within the selected route.

## Paper revision

The paper now follows the completed 235 argument:

1. The exact square identity `T + 2 s0 + 35(m+1) = 9214`.
2. The completed six-centre catalogue and potential, including the six initial internal counts and both endpoints.
3. The estimate `4m <= T+21` and retained inequality `39m + 2 s0 <= 9200`.
4. The immediate conditional target: eighteen empty squares suffice for 234.
5. The checked short-return restrictions, full pair-cap catalogue, five share inequalities, reversal and overlap accounting, and conditional finite-block estimate.
6. The exact finite-model comparisons and the zero-credit limitation, with unreplayed premises identified explicitly.

The earlier 236 proof is preserved in an appendix. All 95 previous statement blocks remain, except that the main interval is strengthened to the completed contributor result. The revised source contains 108 statement blocks. Thirteen complete printed snake witnesses pass 118,673 pair checks; the two added return witnesses also pass exact singleton-count and transition-pattern checks. All labels and citations resolve in the source. Authors and hyperlink settings are unchanged.

The manuscript does not claim a new global bound from the share computations. The conjecture 196 remains unproved. It continues to distinguish complete-snake witnesses, local forests, checked refutations, conditional arithmetic, and exploratory finite-model claims.

## Compilation limitation

The built-in editor compiler was called on the saved editor source. Both attempts failed before TeX source processing because the Windows compiler helper could not enforce its requested writable-root configuration. The exact diagnostic is in `data/compiler-diagnostic.json`. Source structure checks pass, but PDF compilation and visual inspection of this revision are unverified. No replacement document or separate PDF was created.

## Reproduction

- `scripts/prepare.py`: reconstruct the saved zero-credit cycle and its Lean arithmetic source.
- `scripts/check_lean.py`: check both new modules in a fresh build using the pinned Lean 4.19 environment.
- `scripts/revise_paper.py`, then `scripts/finalize_paper.py`: one-time source transformations from the pinned pre-revision manuscript; the first script refuses a different starting hash.
- `scripts/verify.py`: source integrity, complete printed witnesses, actual graph-cycle membership, source/build hashes, and the ten standard-axiom audits.
- `data/verification.json`: final verification receipt; `data/paper-revision.json`: manuscript provenance; `data/zero-credit-cycle.json`: finite obstruction.

GitHub was refreshed in this round. Main remained at `c6246609` before this commit; the contributor branch remained at `74ca83db`. No newer contributor result was adopted. The archived 235 audit is pinned at `b20346ee`.
