# Boundary contribution and weaker share requirements

## Checked deduction

Let m count snake edges, T be the total singleton count, sigma_i the nonnegative integer empty-square shares, and L the physical rounding loss. Keep the existing six-step table and its original weights. Put N=m-7. At step n the table weight is 120 b_(n+7)+S_n, where b_i<=alpha_i. Require only S_n<=sigma_(n+3)+...+sigma_(n+7)+q, and let W be the sum of these original weights.

Six omitted internal counts contribute at least 14 and the two endpoints at least 8. Thus the retained count sum is at most T-22. Each physical share occurs in at most five windows. Consequently

    W <= 120(T-22)+5 sum(sigma_i)+q(m-7).

Substitute the exact identity 24T+sum(sigma_i)+840(m+1)+L=221136:

    W+4200m+5L <= 1098840+q(m-7).

This improves the contributor's omitted-count contribution from 14 to 22, gaining 120*8=960 units. The original finite potential and original table weights are retained; only the geometric share requirements are weakened.

The B233 potential has slope 520. Its existing 10-bit representation gives range at most 1023, hence 520(m-7)<=W+1023. With q=4:

    4716m+5L <= 1103475.

At m=234 the left side is at least 1103544, a contradiction by 69. Thus m<=233 under the stated premises. If the sharper range 784 is certified, q=5 gives 4715m+5L<=1103229, excluding 234 by 81.

Both deductions pass Lean for arbitrary natural-valued sequences. They do not yet identify the contributor's complete actual-snake semantics with these sequences. That integration remains a separate task.

## What larger slack requires

With q=5 and range 1023, any m>=234 would force L<=31. Therefore five-point slack suffices when L>=32 in that hypothetical case. Equivalently, five-point requirements may be used generally if four-point requirements can be proved whenever L<=31. These implications also pass Lean.

The earlier actual-snake theorem says an undominated cube vertex contributes at least 96 to L. Consequently the remaining low-loss case is dominating. This provides a geometric restriction for the hybrid argument; it does not establish the stronger local shares in that case.

The scalar pair m=234,W=117017,L=0 satisfies the q=5, range-1023 premises. The pair m=234,W=117256,L=0 satisfies q=6, range-784. These examples are Lean-checked arithmetic limitations, not snake constructions or counterexamples to the geometric statements.

## Finite table consequences

The exact saved table has 23,783 share rows, including 490 rows requiring paid certificates. Reducing every requested level by four, with a floor of zero, makes 31 of these rows follow from nonnegativity or established universal share-16 floors: 17 level-four rows and 14 level-twenty rows. This leaves 459. If the critical 012034 floor fifteen is completed, another 53 rows become covered, leaving 406. With five-point slack the corresponding counts are 459 and 399.

Two more established floors, share twelve for 012310 and for six distinct directions, cover 33 additional paid rows. Their source and object hashes match the earlier integration receipt. Sixteen of these rows already follow at the original level; seventeen need the new slack. Thus the complete census using these six universal floors leaves 426 paid keys, or 373 after the critical floor fifteen is completed (366 with five-point slack). The earlier 459/406/399 figures deliberately use only the four universal share-16 floors already ported into Floors233. See data/floor12-census.json for the added rows and evidence.

These are native table counts. The relaxed lookup wrapper and complete coverage proof have not been checked in Lean, the older full dependency closure was reused rather than rebuilt, and no runtime saving has been measured. The plain/H8 certificate obligations are unchanged.

## Contributor evidence and current limits

The inspected contributor revision is e7b21e0c8704b716115cda60a05e3b4c5d1c059f on research/unconditional-241. Its saved source and Linux log give a conditional 233 chain using the established share floors. The production update reports all 204 automaton shards compiled and all 6,163 new certificate cores generated: 5,673 plain/H8 and 490 share. Full production refutation replay and assembly remain pending. This round inspected and preserved that evidence; it did not independently rebuild that chain locally.

The project interval remains 191--235, with the archived 235 proof's complete independent rebuild pending. There is no new unconditional upper bound, longer construction, or proof of 196.
