# Review of the shortened frontier explanation

Reviewed all 353 lines of paper/snake9_frontier_explanation.tex, without editing the source or running searches, tests, compilers, or calculations.

Reviewed source SHA-256: 66f932f058ab71a5d26dbecf8ded78fd84e2cc833cd129adf31c2677cc829685.

Comparison basis: the previously inspected complete construction discussion in milestones/210-paper-review/data/research-before.tex, lines 6301–10200, including the round 201–209 arguments and the saved milestone 201, 205, 207 and 209 records. Before-snapshot SHA-256: 4e902994337c8ef30d3d308e6915d7d43a80cb357570926fa23ab5fb42b8f73a.

The shortened explanation preserves the main distinctions between written arguments, checked components, literal finite coverage, native exclusions, and unresolved global conclusions. The following local wording changes would make the mathematical assumptions explicit.

## Corrections

1. **Lines 108–120: give the length assumption for the window comparison.** The text begins with only \(m\ge1\), while this comparison uses nine-transition windows, seven omitted internal counts, and \(m-8\) windows. Change the opening to: “For \(m\ge9\), consider the retained nine-transition comparison, and let \(W\) be its total window weight.” Add that shorter snakes already satisfy the candidate upper bounds. The displayed comparison need not change.

2. **Lines 189–197: restrict \(e\) to the original parent edges.** Original opposite-face vertex sets may already create cross-edges, which the identity does not include in \(e\). Replace “\(e\) original edges deleted at both ends” with “\(e\) original within-face parent edges whose two endpoints are deleted”. The existing accounting identity is correct with this definition. The two parents are correctly assumed to have positive length.

3. **Lines 240–242: include the possible global parity change in the Q2 classification.** Component switches preserve the free-word parity; targets with the other constant parity offset also exist. Replace the first sentence with: “With two free coordinates, after a single global free-coordinate bit flip if needed, independent component switches describe every induced target with the same indexed retained words.” The connected-component conclusion then holds as written. The full argument in the before snapshot includes this normalization.

4. **Lines 243–246: specify both relations in the Q3 extension hypothesis.** “Adjacency correspondence” is insufficiently precise for the extension argument: an injective map preserving edges alone can introduce edges among formerly nonadjacent selected vertices. Replace the opening with: “In three free coordinates, every injective parity-preserving map between selected subsets that preserves adjacency and nonadjacency extends to an isometry.” The partial antipodal-label argument then has its required hypothesis.

5. **Lines 172–176: identify the two endpoints of the middle path.** “Its designated joining endpoint” leaves the endpoint ownership ambiguous. Replace the hypothesis with: “If \(P,R\) are disjoint and nonadjacent, and the projected intersections of \(Q\) with \(P\) and \(R\) are singletons comprising the two distinct endpoints of \(Q\) and one endpoint of each outer path, the result has …”. A projected intersection at an internal vertex of \(Q\) would produce an unwanted degree-three vertex.

6. **Lines 318–321: express the capacity premise in terms of assigned words.** Replace “any subset of pairwise-distinct variables” with “any subset of interval variables whose assigned words are required to be pairwise distinct”. Distinct variables alone can share a value; the capacity statement requires a pairwise distinctness constraint on their values. This is a prospective consequence, and the text correctly does not claim that the stronger rule has been implemented.

## Small clarifications

- **Lines 91–103:** introduce \(S\) as the selected vertex set before its first displayed use.
- **Lines 240–249:** add a short proof-status sentence, such as: “These classification and extension arguments have checked components; their complete geometric assembly is a written proof.” The before snapshot explicitly reserves this distinction. The preceding checked generic slice criterion and literal model coverage do not automatically certify every subsequent classification argument.
- **Lines 263–265 and 284–298:** call the merged intervals maximal. A brief clause that successive intervals are joined by a free-coordinate edge explains why their free-word parities alternate. Write “\(N_z\) counts singleton intervals at \(z\)” instead of “singleton visits”, and state \(r\ge1\) in the general capacity statement. These clarify which objects are counted without introducing a new definition.

## Claims retained correctly

- Lines 233–238 distinguish the native census over all 254 partitions from checked literal coverage, and explicitly retain the unfinished geometry/domain and surviving-leaf connections.
- The adjacent-slice criterion in lines 221–229 is the correct two-part condition: existing projected coincidences are fixed pointwise and additional projected coincidences are forbidden.
- Lines 199–212 retain the two-parent, deletion-only scope and the source-specific 52-vertex obstruction. They do not exclude all possible Q8 or Q9 constructions.
- Lines 269–281 restrict the four- and five-history exclusions to the saved source, the same length, and fixed index matching. The completed retained pair (1,4) is distinguished from the other 27 six-free-coordinate models.
- The square-capacity inequality in lines 291–298 is correct: the multi-visit intervals and the larger singleton family from each opposite-corner pair require distinct words of one parity. Its \(2^{r-1}\) capacity concerns those equal-word conflicts; full inter-parity constraints remain necessary.
- For the saved (0,5) counts in lines 300–305, the 32 representative intervals exhaust the 32 even words. The remaining five and four singleton intervals must pair with opposite-corner representatives, yielding exactly nine doubled words. Individual pairings remain undetermined.
- Lines 311–331 correctly limit the Lean claims to geometry, generic implications, literal interval data, and generic frontier coverage. They do not equate hashes or state-transition audits with certification of the entire native traversal.
- Lines 333–344 preserve the difference between a new Q8 parent, a checked Q9 joining construction, and an optimality proof. The 197-edge prefix exclusion criterion is correct.

No numerical or global-bound conclusion is added by this review. The upper-bound coefficient displays were read for consistency and logical scope; this review did not independently rebuild their finite graph certificates.

## Final-version review

Read all 361 lines of the revised paper/snake9_frontier_explanation.tex. Final source SHA-256: b9a0547bfc5fe09362236e0b11ff51e17b0adc9f3c441a66051629dbb7194044.

All six correction findings above are resolved:

- Lines 109–138 state the window-length assumption and cover shorter snakes.
- Lines 192–194 restrict the deleted-edge count to original within-face parent edges.
- Lines 244–248 include the uniform parity offset and identify the remaining complete Q2 Lean assembly.
- Lines 248–251 specify injectivity, parity, adjacency, and nonadjacency in the Q3 extension statement.
- Lines 175–179 identify the distinct joining endpoints of the middle path.
- Lines 325–329 require pairwise distinct assigned words for the proposed capacity strengthening.

The smaller notation and interval clarifications are also present: S is introduced at line 92; maximal intervals and alternating parity are explained at lines 269–271; singleton intervals are counted at line 299; and r >= 1 is explicit at line 305. The final version continues to distinguish literal finite coverage from geometric interpretation, native source-specific exclusions from general classification, and the capacity deduction from a complete search certificate.

No additional correction is required within this review's scope. No source outside this review log was edited, and no searches, tests, compilation, or new certificate verification were performed.
