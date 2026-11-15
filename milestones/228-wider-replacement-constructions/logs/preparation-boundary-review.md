# Width-45 preparation and conditional boundary-cut review

Read the complete `prepare_width.py` and `joint_boundary.py` sources. Independently reconstructed the immutable width-45 preparation and checked the copied width-44 closure premise and its pins. No blocking issue was found for the current width-45 batch. No solver, compiler or software test was run, and no mutable batch results were read.

## Index coverage and prepared domains

The 308 contexts are exactly the pairs of intervals $[a,a+45]$ and $[c,c+45]$, where $a=0,\ldots,6$ and $c=99,\ldots,142$. The seed has 192 distinct vertices and is induced. Its vertices adjacent to proposed endpoint 24 occur exactly at indices 7, 143 and 191; index 191 is the intended attachment endpoint 88. The two unwanted blockers must therefore be removed from open replacement interiors. Their separation prevents one block of at most 45 edges from containing both.

Every shorter aligned two-block replacement with both lengths at most 45 can be padded with unchanged original segments into this grid, provided it removes those blockers. For a first interval $[l,r]$, choose $a=\max(0,r-45)$. The conditions $l<7<r$ and $r-l\le45$ give $a\le l$ and $0\le a\le6$. For the second interval choose $c=\max(99,r-45)$; its blocker and length conditions give $c\le l$ and $99\le c\le142$. These padded intervals remain disjoint: the first ends at most at 51 and the second begins at least at 99. Padding preserves the whole candidate and its crossing count. This is coverage of the specified fixed-seed, retained-anchor/outside, length-preserving family.

All 616 initial domains were independently reconstructed from the retained vertices, their forbidden neighbors and endpoint 24. Repeated nonanchor degree-below-two deletion and anchor-connected-component restriction were recomputed using a separate fixed-point procedure. Every resulting allowed list and rejection reason matches. A 45-edge path has 46 vertices and therefore 23 of each parity; every part has the correct target and colour requirement. The saved classification is exactly 107 `STATIC_EXCLUDED` and 201 `PENDING` contexts.

These restrictions are necessary. A replacement interior cannot repeat a retained vertex, touch a retained nonanchor, repeat 24 or touch 24. Restoring the prescribed original anchors accommodates their required boundary edges. An internal simple-path vertex has two distinct path neighbors, and all path vertices lie in the anchor component. Component size and colour shortages therefore justify rejection.

The preparation reads no smaller-width exclusion table and emits no inherited-exclusion rows. Every crossing budget was recomputed as four minus the unchanged seed crossings. No width-44 exclusion is transferred upward to a wider domain.

## Boundary-cut justification at width 45

Assume the complete native exclusion of all width-44 contexts for this same seed, endpoint and four-crossing construction. In an actual induced width-45 replacement, selecting the old vertex immediately after its left anchor forces that vertex to be the first successor: it is adjacent to the anchor, and any later position would create a chord. Removing that unchanged boundary edge gives a 44-edge replacement with the next original vertex as its new anchor. The corresponding statement holds at the right end.

If neither block omits both original boundary neighbors, each block permits at least one such trim. Trimming once in each block retains exactly the same full 193-vertex candidate and gives two width-44 replacements. A trim cannot expose blocker 7 or 143 as a retained anchor, because either blocker is incompatible with appended endpoint 24 and cannot be selected. Both trimmed intervals still contain their blocker strictly and lie in the covered width-44 grid. Trimming a crossing edge merely moves that edge into the fixed part, leaving the total four crossings unchanged. This would contradict the width-44 premise.

Thus at least one width-45 block must omit both old boundary neighbors. The model's selectors encode precisely this disjunction: selecting a block's auxiliary Boolean forces each of its present old boundary variables to zero; an absent boundary vertex is already omitted. A converse constraint on the selector is unnecessary because its value is free to witness the disjunction.

The finite audit checked all 942 available individual trims and every pair of trims from the prepared domains. All mapped into the covered width-44 grid. There are 203 contexts with an available trim on both parts, including all 201 pending contexts.

The local closure file is byte-identical to round 227's completed coverage, and the new input uses the identical seed and endpoint. The cut is conditional on that native exclusion. It need only hold for actual connected induced paths; it may remove disconnected selections allowed by the degree relaxation.

## Remaining source scope

Selected counts, induced degrees, alternating parity and cross-part nonadjacency retain their necessary interpretations. Per-part crossing parity agrees with its anchor face bits. For same-face anchors, fewer than 46 available vertices in that face rules out zero crossings and justifies a minimum of two. The previous lazy-cycle procedure and full 193-vertex witness validation remain unchanged.

The worker still contains an `INHERITED_EXCLUDED` branch inherited from an earlier source. It is unreachable on the audited input and supplies no exclusion here.

One limitation matters for future use: `prepare_width.py` accepts widths 45–50, while `joint_boundary.py` does not enforce `width == 45`. The present boundary cut follows from the width-44 closure only at width 45. At width $w>45$, trimming one edge leaves width $w-1>44$, so the same contradiction does not follow. The current width-45 run is within the justified scope. Reusing this worker at widths 46–50 requires a stronger preceding-width closure or a different boundary condition; its general command-line argument does not establish that justification.

This review establishes no current native outcome, new witness, wider-family exclusion or global upper bound. The boundary cut inherits native rather than Lean contradiction evidence, and the complete model/traversal has no end-to-end Lean certificate.

## Source pins

- `scripts/prepare_width.py`: `391211994dabe1770ea0db0cd0be97f461f4262736a70f294a31c35d49bdc4be`.
- `scripts/joint_boundary.py`: `aefe0c87dcc80f2fdaaf3841703651227bde01cffb5f54b50c72e6144a985c72`.
- `data/regions45.json`: `e64a1de95fe6354ec64e8a5bfc51457bafc262f581df1188a1683978c26d5bb9`.
- Copied `data/coverage44.json`, identical to round 227: `f02bfee405ddc56db3923d246ea245c035f9fa19bb6132923524d46ff64e01a5`.
- Round 227 `data/regions44.json`: `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b`.
