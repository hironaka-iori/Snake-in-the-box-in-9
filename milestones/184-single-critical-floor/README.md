# Round 184: only the critical pending floor must reach fifteen

This completes the second of the two requested rounds, 183 and 184. Publish the saved work and pause the goal; do not begin round 185.

The new sufficient pending-share profile is **(15,14,14,14)**, in the order 012034, 012301, 012340 and 012345. Under the inherited local and retained-graph premises, it gives the conditional upper bound 234 without any positive-loss assumption. This weakens the previous loss-free requirement that all four pending floors reach fifteen.

The maintained project range remains 191–235, with the archived contributor 235 proof's complete independent rebuild still pending. The numerical bound 234 is conditional on unresolved geometric and certificate requirements. No longer construction or proof of 196 is claimed.

## Derivation

The actual-square budget and boundary packing from round 175 give

\[
G+840(m+1)+L\le221136,\qquad W+2880\le5G.
\]

Here (L\ge0) is the actual total share loss. A retained-graph potential with mean (mu) and range (R) gives (mu(m-8)\le W+R). Eliminating (G,W) therefore yields

\[
(4200+\mu)m+5L\le1098600+8\mu+R.
\]

The refined potential has

\[
\mu=\frac{4454}{9},\qquad R=\frac{5421}{9}.
\]

Substitution gives

\[
42254m+45L\le9928453.
\]

Since (235\cdot42254=9928453+1237), nonnegative loss already implies

\[
m\le235-\frac{1237}{42254}<235,
\qquad m\le234.
\]

The earlier potential in this round, with scaled mean 4453 and scaled range 5402, also passes every edge and gives the weaker comparison (235-1029/42253). Its record is preserved; the refined result is the current comparison.

## Exact finite-graph verification and optimality

The producer reconstructs the retained weights from the original graph columns and local rules. It reproduces three archived weight hashes before applying the new profile. Both accepted potentials were scanned over all 4,661,572 retained edges with exact integer arithmetic and zero violations. The source-column caches remain local. The streamed producer peaked below 91 MB private memory under its existing 512 MiB cap and 768 MiB free reserve.

Independent scalar reconstruction checks the concrete cycle and walks against original source rows. The refined potential has a nine-edge cycle of weight 4454 and a 24-edge walk of weight 11275. Their potential inequalities imply

\[
9\mu\le4454,\qquad R\ge24\mu-11275.
\]

Consequently every nonnegative rational mean and range for this fixed graph, boundary and zero-occurrence-credit comparison satisfies

\[
\frac{1098600+8\mu+R}{4200+\mu}
\ge\frac{1087325+32\mu}{4200+\mu}
\ge\frac{9928453}{42254}.
\]

The middle expression decreases with (mu), because (32\cdot4200<1087325). Its minimum occurs at the permitted maximum (mu=4454/9), where the 24-edge walk forces (9R\ge5421). The new potential attains both constraints. Thus its displayed loss-free comparison is optimal for this fixed profile and accounting. This does not establish optimality of snake length or exclude stronger geometric arguments.

Fifteen is the least sufficient integer floor for 012034 when the other three pending floors stay fourteen and this fixed loss-free comparison is used. At floor fourteen, the earlier nine-cycle and eight-edge walk force (9\mu\le4448) and (R\ge8\mu-3356), which keep the loss-zero comparison strictly above 235. Decreasing that floor only weakens edge weights and cannot improve a valid comparison. The denominator-cleared arithmetic is checked in `SingleCritical184.lean`.

An initial witness script incorrectly expected the earlier cycle to gain five units; reconstruction rejected that expectation. It gains six, giving weight 4454. The corrected extraction supplies both the attaining cycle and the 24-edge range witness. The failed script and correction record are preserved. No optimality claim rests on that rejected expectation.

## Proof status and remaining work

`data/SingleCritical184-audit.json` records five accepted Lean dependency reports: the budget comparison, integer upper bound, mean/range optimality, endpoint arithmetic and the floor-fourteen obstruction. The separate actual-snake wrapper keeps the truncation, physical-share identification, local-window lower bounds and potential inequality explicit. It also passed Lean, including the short-length case, with the local-window and potential assumptions explicit. The two modules have six accepted theorem dependency reports. An initial startup stop is preserved separately; no resource guard was changed.

Native contradiction certificates now exist for every numerical floor required by this weaker profile. The 012034 floor-15 proof was reduced in round 183 to 12,424 input clauses, 52,489 deductions and 5,342 variables. The other three floor-14 proofs have complete native replays. The 012301 input uses the necessary extension condition, valid for snakes with at least seven edges; shorter paths already satisfy the intended global bound. The full Lean contradiction and geometric interpretation chains remain unfinished.

The retained count and graph assumptions also remain: the hypothetical 0123104 six-count floor 25 under its exact first-count condition, 1358 reference entries, 791 context obligations and the complete graph-to-snake and finite-edge certificates. The native graph scan cannot prove these assumptions. The older share-18 Lean replay remains separate at 33,111/145,215 deductions.

The loss-zero and loss-one cases no longer need a separate exclusion for this new sufficient profile. They remain relevant to the alternative route using only floor fourteen. The independent empty-square route still targets fourteen empty squares in a hypothetical 235-edge snake.

## Continuation after the requested pause

Complete the Lean and geometric proof chain for the weaker profile before pursuing higher local floors solely to improve this comparison. The compact 012034 certificate is the main new proof input; preserve its original-clause and variable mappings. If a different route is chosen, target a genuinely unresolved inherited graph premise or additional geometry. Retuning the same fixed-profile mean and range cannot improve the comparison proved optimal here.

The manuscripts are updated in the existing D: editor files and mirrored in E:/Snake-in-a-box/paper. Author order and hypersetup remain unchanged. Exact inputs, compressed potentials, source hashes, failed attempts and verification receipts are saved. No next round is started by this handoff.
