# Round 214: parity alphabets and tight partner capacity

The hypothesis was that competition for partners can force restrictions even when every outside interval has individual support. The finite counting deduction is proved, its connection to the normalized source-specific path passes Lean, and a separate native continuation uses it. The case remains open. The numerical interval remains 191<=a(9)<=233, with the contributor233 proof and independent-full-rebuild qualification recorded in round213. No new snake, numerical bound or complete coordinate-case exclusion was obtained.

## Argument

For one parity, C is the chosen family and O the outside family. Assigned words are distinct within each family and belong to a pool of q words. Write s=q-|C|. For J contained in O, N contains every chosen partner that can share a current-domain word with a member of J. The established necessary inequality is

\[
|J|\le |N|+s.
\]

If equality holds, every outside interval beyond J must share with a chosen interval outside N. To prove this, let E consist of outside intervals using words absent from C. The exception budget gives |E|<=s. Every assigned word on J appears among the values on N or E, so

\[
|J|\le |N|+|E|\le |N|+s=|J|.
\]

Equality exhausts those available words. Distinctness within O prevents an outside interval beyond J from using any of them. It cannot be exceptional or share with N. Its actual chosen partner therefore lies outside N, and the partner's fitted domain supplies the retained value. This proves preservation of the same complete assignment under the support restriction.

For a strict example, take a four-word pool {0,1,2,3}, chosen values fixed to0,1,2, and outside x,y each with domain {0,3} and only the chosen0 as partner. With one spare word, {x,y} is tight. Another outside variable z with domain {0,1,2,3} must use1 or2. Every outside variable has individual partner support initially, so the earlier count of individually unsupported intervals alone gives no deduction. This example concerns the finite capacity model; no claim is made that it is itself a full snake instance.

## Connection to the reconstructed path

The literal 99-index source determines77 boundaries between successive free-word groups. At each boundary the retained base is unchanged; the induced-path condition forces Hamming distance one between successive free words. A general Boolean-word lemma proves that such an edge flips parity. Starting the free word at zero gives weight(u_g) congruent to g modulo2 by induction.

The even and odd six-bit pools each have32 words. Lean checks their lengths and the two literal parity masks, then derives actual membership for bounded raw values below64. The bound is essential: decoding six bits of a larger natural number does not determine its actual integer range. Normalization at zero and the range premise are explicit.

Combining this with round213's geometric distinctness and partner completeness gives the tight filters directly from the actual normalized reconstructed path. The even family has30 chosen variables and spare allowance2; the odd family has26 and allowance6. Current-domain fitting, a duplicate-free subset of outside values, candidate coverage, tight cardinality and support containment remain explicit. Complete normalization from arbitrary equivalent inputs, literal native-domain interpretation and traversal certification are unfinished.

Five new modules pass with13 dependency reports. The accepted dependencies use only propext, Classical.choice and Quot.sound. Two early concrete checks stopped for low free memory. Removing an unnecessary large import and keeping a definitionally identical six-bit decoder reduced the input size; the unchanged resource limits were then met. A separate proof attempt exposed two simplification errors; the repaired proof passes. Failed attempts are retained, and only successful audit receipts identify accepted proofs.

## Native continuation

The augmented candidate graph places the chosen partners and s universal auxiliary slots on one side, and outside intervals on the other. Matching is used to discover subsets. A matching failure rejects only after directly checking |J|>|N|+s. Alternating reachability discovers tight subsets, whose actual neighbor cardinality is checked before filtering. Success of this graph matching is never treated as a valid word assignment. Previously computed neighbor sets remain safe during sequential deletions because they overestimate the remaining support.

The transfer preserves726 prior files and all eleven unfinished domain vectors, changing only the engine pins and adding its transfer record. The independent source review found no defect under the saved geometric family assumptions. The120 new jobs ended normally:105 subtrees exhausted,15 limited runs,749,506 nodes and49.130 reported solver seconds. The new partner rule recorded3,054 value removals and120 contradiction returns. These are repeated operations across branches; they establish neither a number of distinct global exclusions nor a speed improvement.

The independently audited saved chain ends OPEN at240 total jobs,13 pending regions and1,801,017 cumulative nodes. Its final state hash is eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027. The earlier round212 state is unchanged. Cases23,24 and9 remain at their previous states. Only retained[1,4] is exhausted among the28 six-coordinate choices;27 remain unresolved. The known191-edge construction and the unresolved196 conjecture are unchanged.

## What to pursue next

Every outside subset in the13 saved regions satisfies the partner inequality; the maximum partner deficiency is1 in both parities, below allowances2 and6. Thus simply repeating the same snapshot count gives no immediate exclusion.

The partner graph ignores competition for the actual word labels. A separate finite-domain analysis finds72 candidate word removals across seven saved regions through tight distinct-word subsets, with no deficient family. Some may follow from existing binary propagation; the analysis does not modify a state or establish a performance gain. The useful next implementation is distinct-word subset propagation for both chosen and outside families, combined with the new partner rule. The generic subset-capacity proof from round211 can be reused. Do not assume that candidate matching supplies consistent labels or a new Q9 snake.

The goal remains ACTIVE. The user clarified that contributor work alone must never trigger a pause. Continue across rounds; a pause may follow a substantial result or prolonged lack of progress in the user's and this agent's own work. No email was sent because no sending connector is available. Both existing LaTeX sources compile and preserve author order and local hyperlink settings, with exact paper mirrors. Last full-paper review210; next scheduled220.
