# Independent alignment and existing-guard review

The new probe correctly represents milestone119 edge18806: direction index2, history0, count code42098, direction word $012031043$, and six count symbols $(6,3,3,6,3,3)$. Its window vertices are

$$[0,1,3,7,6,14,12,13,29,21].$$

The existing `sixSymbols_explicit` theorem in milestone79 places these six symbols at centres $r+3,\ldots,r+8$. Therefore the eight internal-centre bounds

$$[(0,21),(0,21),(6,21),(3,3),(3,3),(6,21),(3,3),(3,3)]$$

have the correct alignment. The first two internal counts are unrestricted; each6 retains the full interval $[6,21]$. The probe uses radius9, hence all512 cube vertices, and adds no sum counter. The saved result is `UNSAT_UNCERTIFIED` in0.063 seconds with zero added cycle cuts. Source hashes agree with the record. This inspection supplies no contradiction certificate or new Lean theorem.

## The earlier $012031$ outer-sum hypothesis

The rule named `012031-upper5-outer15` in milestone119 is

$$\alpha_3\le5\quad\Longrightarrow\quad
\alpha_1+\alpha_2+\alpha_4+\alpha_5\ge15$$

on canonical word $012031$. Its source is milestone112 `data/probes/012031-upper5-outer14.json`: native `UNSAT_UNCERTIFIED`,10.828 seconds. Milestone112's mathematical note explicitly leaves this inequality among the unproved graph hypotheses. The checked theorem `ActualSum112.actual_outer_sum` instead concerns $012314$, middle count at most2, and outer sum at least19. The presence of that checked theorem must not be used to upgrade the $012031$ rule's status.

There are four contained six-transition windows in the new nine-transition word. The three with canonical shape $012031$ give:

| Direction offset | Orientation | Five canonical count intervals | Effect of the earlier rule |
| ---: | --- | --- | --- |
| 0 | Forward | $([0,21],[0,21],[6,21],3,3)$ | Middle count is at least6; the hypothesis fails. |
| 1 | Reversed | $([6,21],3,3,[6,21],[0,21])$ | Middle is3, but the outer sum is already at least15. |
| 3 | Forward | $(3,3,[6,21],3,3)$ | Middle count is at least6; the hypothesis fails. |

The fourth window, at offset2, has shape $012314$ and counts $([6,21],3,3,[6,21],3)$. Its middle count3 fails the hypothesis of the checked middle-at-most2 theorem. Thus neither of these earlier sum statements gives a contradiction from the stated intervals. In particular, the new native UNSAT is not explained by directly applying `012031-upper5-outer15`.

## Reference-catalogue comparison

The review parsed all1378 literal keys from milestone85's22 reference chunks, preserving their exact order and source hashes. It checked every contiguous placement within the nine directions in both orientations. Among1101 shape-matching key placements, none has forbidden count intervals containing the entire corresponding probe intervals. Thus the probe does not directly force a single listed reference key. The full nine-direction word is also longer than the catalogue's individual direction windows.

This is a bounded syntactic containment check. It does not establish independence from combinations of references, additional count propagation, longer contexts, or other geometric facts. The target is already accepted by the saved retained diagram and has zero deficit under the thirteen sum rules in milestone119, which is consistent with the direct checks above. The catalogue's generic `reference_union_refuted` theorem retains its explicit refutation premises; finding a matching key would not by itself close an absent proof.

No novelty claim is made. The precise conclusion is that the proposed full interval window is correctly encoded, and the inspected existing sum rules and single-key catalogue applications do not already exclude it. Radius or guard weakening and a contradiction certificate remain separate work.

## Evidence and scope

`data/target-review.json` records the full key, all four subwindows, old rule status, catalogue source pins and zero direct matches. SHA256: `be3f14852e358a63db158ac30dccfdd9fad7666735706b1486a41e623e974048`.

Principal pins:

- New native probe: `7745a254314f83a95a80e74f2e9ee62095bdc475e60a7992360d8a90c5b75db9`.
- `scripts/probe_window.py`: `dba85e108a6e7b505a062e0ed595e4ea67b745e37591d0aa6ac4120ad16aa753`.
- Milestone119 graph audit: `76a3119d3410330827418c5039203e579ccd27a91c7c9315d786eb78c9bcb177`.
- Earlier $012031$ probe: `0471bff64811b5a990e3a39279ef96b80de0522ae5334485181d804bd27dc444`.
- `ActualSum112.lean`: `9e5f7db4a74440971e5bd3d9ada06c1973c021614df22e94d09aa803d83f759d`.
- `CountWindows.lean`: `ec60fb130f2d25f02da27df5052e48caa09c9a9113de7c6ac5e74295604d01a2`.

No SAT solver, Lean compiler or Git command was run. Only the owned review and evidence files were written; live batches and existing evidence were unchanged.
