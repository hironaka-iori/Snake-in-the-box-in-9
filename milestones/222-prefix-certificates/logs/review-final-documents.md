# Final bounded document review, round 222

No substantive mathematical error was found. The revised documents consistently state the fixed-parent exclusion, its extension to the same cube-isometry class, the 191-edge ceiling without an attainment claim, the unchanged global interval, and the separate scopes of generic Lean results and exact numerical audits. One short explanatory addition to the frontier is recommended below.

This is the requested round-222 revision review. It is not a new full-paper review; the full review was completed at round 220 and the next scheduled full review is round 230. No manuscript was edited, no compiler was run, and no software tests were created or run. Compilation and visual inspection belong to the parent task.

## Exact reading coverage

Read every hunk of both complete diffs against `data/before-snake9_research.tex` and `data/before-snake9_frontier_explanation.tex`. Read the current frontier source in full, lines 1–418. Read the current main abstract, lines 38–87; the complete new subsection `sec:prefix222`, lines 7607–7710; and the complete verification/status section, lines 7711–7881. The revised historical introduction and conclusion of `sec:parity221`, the date, and the added bibliography entry were included in the complete diff review. The main source has 11,332 lines; unchanged portions outside the stated coverage were not reread in this pass.

Read all 51 lines of `MATHEMATICAL_NOTE.md`. Checked the quoted round-222 counts and bounds against the saved prefix/deep audit receipts. Read both complete new Lean sources and inspected their acceptance records, including source, log, and object hash matches. Used the earlier model-validity challenge for the necessity of the frozen numerical constraints. This pass did not repeat the tree or coefficient audits, reconstruct numerical primal certificates, or reprove archived results.

## Reviewed editor sources and mirror equality

The authoritative editor sources are in `D:/Codex/2026-10-13/new-chat/outputs`. Their counterparts in `E:/Snake-in-a-box/paper` are byte-identical. The hashes agree with the parent-provided frozen revision.

| Source | SHA-256 |
|---|---|
| Current editor and mirror `snake9_research.tex` | `0ec5b0ec20672646bec75602ba7530c121f4755f8bd7423c73de727a06c6ba89` |
| Current editor and mirror `snake9_frontier_explanation.tex` | `5c65c9bc7f069d50b95c13df386d32ddb885a84d7c86b69cb1ad0140f70ea4cc` |
| `data/before-snake9_research.tex` | `09a30206191809ba80a7d6ee11af6fcd3fb99e589d84243f970da182a8a170bf` |
| `data/before-snake9_frontier_explanation.tex` | `adbac0716c6ee01d61f2b801e4809d10f19e69c0ee80c04da728378df860873d` |
| `MATHEMATICAL_NOTE.md` | `70fb9a9d59d97eecae767f95c400c1e615f43becaa5197f38d9fe21134ee36ce` |

All 349 earlier main-source labels remain in their original relative order. There are 351 labels after the revision, with no duplicates; the only additions are `sec:prefix222` and `prop:parent191`. All 119 earlier main bibliography keys remain, with `research222` added. The frontier has no labels before or after the revision, and all four earlier bibliography keys remain with the same addition.

Both author blocks are unchanged and preserve Iori Hironaka, Tommy Ma, and Steven Zhan. The main `hypersetup` block is unchanged. The frontier has no explicit `hypersetup` block before or after this revision.

## Numerical claims and finite coverage

The counts in the main subsection, frontier, and mathematical note agree with the audited ledger:

| Prefix edges | Nodes | Excluded leaves | Expanded nodes |
|---:|---:|---:|---:|
| 1 | 14 | 3 | 11 |
| 2 | 33 | 23 | 10 |
| 3 | 21 | 17 | 4 |
| 4 | 9 | 8 | 1 |
| 5 | 1 | 0 | 1 |
| 6 | 2 | 2 | 0 |
| Total | 80 | 53 | 27 |

There are no unresolved leaves. The 53 exclusions comprise three inherited first-step exclusions and 50 new leaf exclusions. The 77 new calculations comprise those 50 leaves and the 27 expanded nodes. The resource history is consistent: 45 completed queries before the interruption, 20 saved pending prefixes, then 29 continuation queries and three deeper queries. The earlier interrupted batch remains identified as interrupted; its individual completed certificates have independent arithmetic support.

Root 0 has 31 excluded leaves and maximum exact leaf bound $9396307/100000=93.963070$. Root 78 has 22 excluded leaves and maximum $93984077/1000000=93.984077$. Their respective strict gaps below 94 are $0.036930$ and $0.015923$.

The sole depth-four surviving prefix is $(78,206,198,196,197)$. Its forced next vertex is 213; the following choices are 215 and 221. The corresponding final exact bounds are $3759179/40000=93.979475$ and $46707409/500000=93.414818$. These are correctly paired in the documents. A depth cap of eight was configured, while the actual completed tree reaches only depth six; the documents use the actual depth.

The retained round-221 upper bounds $95.955197$ and $95.763979$ are historical comparisons. The frontier's exact feasible objective values

\[
q_0=\frac{2507137819890885477}{26128236866583647},\qquad
q_{78}=\frac{388107824092577}{4052758842992}
\]

match the saved long-primal audit and both exceed 94. The mixing weight $92/(q_t-2)$ correctly yields total weight 94 when combined with the corresponding one-edge path. The three complete-family feasibility statements remain about the unconditioned fractional relaxation and are consistent with the Boolean prefix exclusion.

## Mathematical scope

The proof follows an arbitrary compatible 93-edge path through the complete prefix cover to a leaf. Every used prefix has at most six edges, so it is proper and its nonroot vertices cannot be the full path's free endpoint. The selection and endpoint-zero equations are therefore necessary, including at the last vertex of a partial prefix. The hypothetical path selects 94 vertices and contradicts the leaf bound below 94.

Taking a compatible 93-edge prefix of any longer partner justifies the bound of 92 edges for arbitrary partners. This step avoids applying an odd-edge model directly to an even-edge partner. The joining length is then at most $98+92+1=191$.

The inverse-isometry argument preserves inducedness, length, the designated joining endpoint, and avoidance of every other parent vertex. The result consequently applies to the entire cube-isometry class of this saved parent. The new proposition and its surrounding explanation correctly retain the use of the entire 98-edge parent and one crossing. They exclude no different parent class, shorter-parent construction, or multiple-crossing arrangement.

Neither source claims a compatible 92-edge witness or attainment of the restricted 191-edge ceiling. Neither identifies that ceiling with a global upper bound. The maintained interval remains $191\le a(9)\le233$, with the existing independent full-rebuild qualification on the contributor theorem. The round-221 first-step discussion is now explicitly historical, and the abstract and current status point to the complete round-222 exclusion.

The remaining fractional feasible points cause no contradiction. Actual prefix choices impose branch equalities that a fractional point distributed among several choices need not satisfy. The documents state this distinction directly and do not present a fractional assignment as a path.

## Lean and numerical verification limits

The four new generic results are exactly the three theorems in `Prefix222` and `PartnerIsometry222.pullback_partner`. Both saved compilation receipts report `PASS` and exit code 0. The three prefix theorems report `propext` and `Quot.sound`; the isometry pullback reports no axiom dependencies. The inspected theorem statements support the reported continuation, nonendpoint, endpoint-indicator, and inverse-isometry implications under their stated path and map assumptions.

The source, compiler-log, and object hashes match both receipts. This review performed no compiler run. The manuscripts correctly distinguish these generic implications from the concrete model interpretation, finite child coverage, and weighted numerical certificates. They explicitly state that the complete tree and coefficient arrays have no end-to-end Lean assembly.

The stage-one and final deep audit statuses support the quoted finite result. Their numerical work is not repeated here. The separate structural challenge supports the necessity of every saved model row and the prefix restrictions. The mathematical note is consistent with this evidence and states the no-attainment and fixed-parent limitations. Its closing workflow instructions are operational records, separate from the mathematical conclusion.

| Inspected receipt | SHA-256 |
|---|---|
| `data/prefix-audit.json` | `8a070ed47d2d6192ab371ed3b96c78fd24763c89417ae83b95477af97209d2b6` |
| `data/deep-audit.json` | `26c85c628fb83319aac68e78b6911d28841e3382de264bdd6c79988c463920fb` |
| `data/Prefix222-audit.json` | `fa3c84224d5fb0965f49070ae35a96c2695868e361b1e1dc0a944612fd1f8228` |
| `data/PartnerIsometry222-audit.json` | `c4178878f94a61f5e4a17e1463d94439acf1cf3ba81a79a758c38b830fe50664` |

## Recommended explanatory addition

The short frontier moves from adding prefix rows directly to exact upper bounds, without explaining why the numerical certificates prove those bounds. Because this is the central new exclusion, one sentence should identify the exact weighted-row argument. Insert after the sentence “Each branch adds its prefix equalities to the model.” at current frontier line 325:

“Each exact certificate combines inequality rows with nonnegative weights and equality rows with signed weights, then bounds the remaining coefficients using the variable bounds $0\le z_j\le1$; numerical optimality is unnecessary.”

The main manuscript and mathematical note already contain the argument. This recommendation requests no additional computation and changes no mathematical claim. It has not been applied by this reviewer. Final typesetting, compilation diagnostics, and visual layout are outside this receipt.

## Addendum: final explanatory revision accepted

The parent applied the recommended explanation through `scripts/refine_explanation.py`. The preceding review is preserved as the record of the initial frozen version. The revised frontier paragraph at lines 325–329 was reread and accepted. It correctly describes signed equality weights, nonnegative inequality weights, residual bounds from $0\le z_j\le1$, and independence from numerical optimality.

The final frontier has 421 lines. Reversing only this paragraph substitution reproduces the initial reviewed frontier's exact SHA-256, `5c65c9bc7f069d50b95c13df386d32ddb885a84d7c86b69cb1ad0140f70ea4cc`. Thus the exact diff below is the only change after the complete reading. The editor and repository mirror remain byte-identical. The main source is unchanged. All prior metadata and label-preservation conclusions therefore continue to apply.

```diff
@@ -323,6 +323,9 @@
 covers every possible continuation. Lean derives these necessities.
 
-Each branch adds its prefix equalities to the model. Exact cardinality
-bounds below 94 exclude branches; every other branch is expanded completely.
+Each branch adds its prefix equalities to the model. Each exact
+certificate combines inequality rows with nonnegative weights and equality
+rows with signed weights, then bounds the remaining coefficients using
+$0\le z_j\le1$; numerical optimality is unnecessary. Cardinality bounds
+below 94 exclude branches; every other branch is expanded completely.
 The audited counts, with depth measured in prefix edges, are
 \[
```

Final editor and mirror hashes:

| Source | SHA-256 |
|---|---|
| `snake9_research.tex` | `0ec5b0ec20672646bec75602ba7530c121f4755f8bd7423c73de727a06c6ba89` |
| `snake9_frontier_explanation.tex` | `72aa8cea5cc715571e175b11527001fd2c1dc868f0d3ff6453f94ef61a8089c7` |

The sole explanatory recommendation is resolved. No unresolved source issue remains from this bounded review. No compiler or software tests were run by this reviewer; the parent's compilation and visual verification remain separate.
