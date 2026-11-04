# Review of lowering the 012034 floor to 17

The proposed change is numerically unresolved on the retained graph. The accepted witnesses permit an integer range from 603 through 631 at mean 496, which would preserve the conditional integer conclusion 234. They do not establish feasibility. The existing potential cannot be transferred by a constant shift or affine rescaling while preserving that conclusion.

This review changes only the conditional 012034 floor from 18 to 17. It retains the milestone-144 mask, all other floors, suffix-only share-17 recognition, the shared count bonuses and zero uniform occurrence credit. Lowering this assumption would not improve the existing numerical comparison; the purpose would be to weaken one pending geometric premise while retaining a comparison below 235.

## Effect on the accepted witnesses

Exactly one of the nine walk edges changes: source row 4684655 has suffix shape 012034, source weight 362, final count 3 and zero shared bonus. Its weight decreases from 378 to 377. The other eight weights remain unchanged. The total becomes 3861, so

\[
R\ge9\mu-3861,\qquad R\ge603\quad\text{at }\mu=496.
\]

The fourteen-cycle contains zero 012034 suffixes. All fourteen weights are unchanged, its total remains 6944 and its mean cap remains \(\mu\le496\). Both witnesses continue to contain zero recorded low-pair occurrence events.

At mean 496 and zero uniform credit, the comparison is

\[
235-\frac{632-R}{4696}.
\]

Consequently, an integer certificate preserving a comparison strictly below 235 would need \(603\le R\le631\). The value 603 is a necessary lower bound from the selected walk, not an established optimum. Even if 603 were attained, the comparison would worsen from \(235-30/4696\) to \(235-29/4696\).

## Cheap certificate transfers

The saved potential was read in bounded blocks, its raw hash was checked, and only the ten walk-vertex values were retained. Along the walk those values are

\[
(602,358,240,240,240,360,360,360,240,0).
\]

All nine original inequalities are tight. The changed second edge therefore acquires slack \(-1\) at mean 496. Keeping the potential or adding a constant fails immediately. More generally, every edge weight decreases by at most one, so the recorded potential remains feasible at mean 495 and range 602. This automatic transfer gives

\[
\frac{1098960+8\cdot495+602}{4695}
=235+\frac{197}{4695},
\]

which does not retain the conditional conclusion 234.

Affine rescaling also fails. Let \(\pi'=t\pi+b\), with \(t\ge0\); its range is \(602t\). The changed edge 4684655 and unaffected edge 491026 impose, respectively,

\[
\mu\le377+118t,\qquad \mu\le616-120t.
\]

For a comparison below 235 the strict margin would have to satisfy

\[
227\mu-111960-602t>0.
\]

The two selected inequalities alone bound this margin above by

\[
\max_{t\ge0}
\bigl(227\min(377+118t,616-120t)-111960-602t\bigr)
=-\frac{10351}{119}<0.
\]

The maximum occurs at \(t=239/238\), where \(\mu=58964/119\). Negative scaling cannot help: the first inequality gives \(\mu<377\), already insufficient with any nonnegative range. Hence no affine transform of this saved certificate can preserve the target comparison, even with the mean retuned. Nonuniform state corrections have not been tested.

## Earlier floor-17 obstruction

The archived milestone-97 floor-17 record contains a 51-edge walk of weight 24663 and deficit 633. All of its rows survive the milestone-144 mask. However, recomputing the present count bonuses from its saved direction indices and count codes adds 1056. There are no suffix share-17 matches. Its current weight becomes 25719 and its deficit at mean 496 becomes \(-423\). Therefore the archived floor-17 obstruction does not transfer to this profile. Its original three-cycle also has two deleted rows; the accepted fourteen-cycle supplies the surviving mean cap independently.

This calculation reused the archived row data and the accepted audit's scalar bonus formulas. The original graph columns were not reloaded for those 51 rows during this review. It is a bounded rejection of a proposed obstruction, not a complete feasibility check.

## Next experiment and limitations

An additional finite-graph check would be justified only as a bounded feasibility experiment for the weaker assumption. A suitable target is mean 496 and integer range at most 631, beginning with the saved potential and allowing nonuniform corrections. A successful outcome requires an exact check of every retained inequality under the revised weights. A failure to repair within a chosen budget remains unresolved unless a retained walk or cycle supplies an exact obstruction. Complete range optimization is unnecessary if the sole objective is to retain a comparison below 235.

No full graph load, full graph scan, optimizer, solver or Lean process was run. Accepted evidence was not modified. Only this review was written. The count rules, six-count assumption, other pending share floors, reference obligations and graph-to-snake interpretation remain conditional.

## Input hashes

SHA-256 values:

- `review/walk-audit.json`: `5b092391a59ab25ced463074a4014beee4072d7f1299071899501feb8d737fbc`
- `data/share17-range496/result.json`: `f6ece94e6d284d0ee735913c4fe0c39a13a3eda27fb3fbab54b518403036850b`
- Saved potential archive: `95f57387e714339d4d55d0bc916597920af6b90de9cf5cd62d0296659c8a2dab`
- Saved raw potential: `04effe853d3846049e1a300f90404a4a66df79498586a34d2aa92a1a5f0bb4b8`
- Milestone-97 `012034-minimum/floor17.json`: `ab46cfe7e456f3bc8e0b70b1be1b67f2ed257c0d8b5fd42a22974da2707a75d9`
- Milestone-120 `full-rules.json`: `dae2b8fc4c807501037041ffada61d80cda1acbf03a3b4536c84338d444a2f57`
- Milestone-144 retained-mask removal list: `b29c2d2717b5d2e1cfefb95b827b1aa0f59376e0fbcdaf693e5553ddf85e82f9`
