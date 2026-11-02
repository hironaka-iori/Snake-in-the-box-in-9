# Combining the saved history share bounds

Let a snake have (m) edges and let (r+9\le m). The five centres charged by the history rules are (r+4,\ldots,r+8). Write their existing scale-12 shares directly as

\[
\sum_{i=0}^{4}s_{12}(p,r+i+4).
\]

Milestone 94 determines every compatible eleven-direction word for each of the 55 saved history signatures. There are 69 words in total. A signature can receive a geometric lower bound only after that bound is proved for every compatible word. This requirement matters for the 14 signatures with two words.

For an emitted signature the eleven-direction window starts at (s=r-2). Thus a local theorem charging offsets (6,\ldots,10) charges exactly the five centres above. Coordinate permutation preserves the theorem, and the canonical direction word supplies the required permutation. The Lean transport theorem checks this change of coordinates and indexing.

Eight rules have stronger bounds under additional count caps. A cap at six-count position (k) concerns the count at (r+k+3=s+k+5), so it occupies position (4+k) in the ten-entry list of internal-window bounds. The transport requires (k<6) and a cap strictly below six. Under this condition,

\[
\min(6,\alpha_{r+k+3})\le c
\quad\Longrightarrow\quad
\alpha_{r+k+3}\le c.
\]

All unused positions retain the universal internal bound 21. In particular, the saturated value six cannot be interpreted as an exact count.

Each applicable geometric or capped lower bound concerns the same share sum. Consequently their maximum also bounds that sum:

\[
\max\{\text{applicable saved lower bounds},0\}
\le \sum_{i=0}^{4}s_{12}(p,r+i+4).
\]

Taking a sum of overlapping alternatives would require an additional disjointness or multiplicity argument. The checked evaluator uses the maximum throughout. A rule contributes zero when its signature is absent. When its signature is present, its geometric bound applies; its stronger bound is also considered when all of its caps hold.

One legacy geometric bound uses a nine-direction suffix of the eleven-direction word. Its local centres have offsets (4,\ldots,8) from (r), so they agree with the same charged sum. The suffix transfer must be checked separately from the stronger eleven-direction bound for that rule.

The local sources were written in several earlier proof environments. This milestone preserves their proof text under recorded import changes and one consistent namespace substitution, then checks the resulting sources in the current environment. Historical successful checks alone do not certify the changed sources. A completed instance is also imported with the defined graph to test compatibility with the intended global argument.

All 69 geometric word bounds and eight stronger capped bounds have now passed Lean. They supply every local premise in the 55-rule assembly, whose final theorem bounds the maximum contribution for every actual snake with a fitting window. The final assembly also imports the defined graph. An independent literal comparison checks the order, signatures, compatible words, caps and numerical credit values against the saved model.

This step supplies one component of the graph weights. The remaining weight components, retained-transition interpretation, pending local exclusions and complete potential check remain separate obligations. It supplies no new numerical upper bound by itself.
