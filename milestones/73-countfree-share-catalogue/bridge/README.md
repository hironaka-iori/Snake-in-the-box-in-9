# Core share and the global square budget

Checkpoint: 2 November 2026. Status: **Lean-checked**, with the source and axiom audit in `data/proof-audit.json`.

## Result

For every snake with edge length \(m\), every nonnegative integer resolution \(M\), and every path index \(k\le m\), the certificate quantity `coreShare M p k` equals the global corner share `shareN M p (p.vertex k)`. Its complete path sum satisfies

\[
\sum_{k=0}^{m}\sigma_M(p_k)\le M E_{\mathrm{anch}},
\]

where \(E_{\mathrm{anch}}\) counts empty squares once at each of their four corners. Consequently this is the usual \(4Ms_0\) budget when \(s_0\) counts empty square faces.

Writing \(T\) for the total singleton-square count, the weighted incidence inequality for \(m\ge1\) becomes

\[
2MT+\sum_{k=0}^{m}\sigma_M(p_k)+70M(m+1)\le18428M.
\]

In particular,

\[
24T+\sum_{k=0}^{m}\sigma_{12}(p_k)+840(m+1)\le221136.
\]

The compiled theorem names are `Snake9.CountFreeBridge.shareN_eq_coreShare`, `core_share_total_le`, `core_share_charge_le`, and `core_share12_charge_le`, in `lean/CoreShareBudget.lean`. The first two count-identification lemmas also check independently: `emptyAt_eq_emptyCount` and `selDeg_eq_cnt`.

## Provenance and verification

The essential bridge was already supplied by the contributor branch `research/unconditional-241`, in `work/spectral/stronger/ShareBridge.lean`, introduced by commit `fcf16838`. This checkpoint recovers that work rather than claiming a new mathematical discovery. Exact sources are pinned at `cd0c90fddf12170d735ee34fcc501e99c60632a6`, with hashes in `data/provenance.json`.

The original contributor modules are preserved under `upstream/`. `CoreShareBudget.lean` extracts their elementary identifications into a separate namespace and adds a small wrapper. It avoids importing the unrelated aggregate-bound certificate chain. The pinned `ShareCharge.lean` agrees, after line-ending normalization, with the source previously retained in milestone 27.

`ShareCharge`, `CoreShareBudget`, and `FiveCentreOverlap` were freshly compiled with Lean 4.19.0. All sixteen printed theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`. The audit rejects unchecked proof placeholders and native evaluation shortcuts. Cached cube and local-window support is reused; this checkpoint does not claim a fresh rebuild of every inherited dependency.

Run `scripts/prepare.py`, then `scripts/check.py`, then `scripts/audit.py` with the repository's configured Python runtime. The build uses one Lean process at a time. Sources are pinned; build paths and dependency hashes are retained in `logs/build-record.json`. The repository's existing Lean and mathlib installations are required.

## Five-centre overlap accounting

`lean/FiveCentreOverlap.lean` proves the generic natural-number inequality

\[
\sum_{0\le r<m-5}\sum_{i=0}^{4} f(r+i+1)
\le 5\sum_{k=0}^{m}f(k),\qquad f:\mathbb N\to\mathbb N.
\]

Here subtraction in the index bound is truncated at zero, so the statement also covers paths shorter than six edges. The proof interchanges the two finite sums. For each fixed offset \(i\), the shifted range is contained in the whole path, and its nonnegative sum is no larger than the whole-path sum. Summing the five comparisons gives the factor five.

The relevant precedent is milestone 27's general `weighted_window_packing`. Its exact reference source and hash are retained in `data/overlap-reference.json`; that module is not an additional compilation dependency. The interval proof supplies the capacity calculation directly.

Both finite-set and list forms are checked, together with the specialization `core_share_five_centre_overlap`. Combining this with the resolution-12 budget proves

\[
120T+
\sum_{0\le r<m-5}\sum_{i=0}^{4}\sigma_{12}(p_{r+i+1})
+4200(m+1)\le1105680
\]

for \(m\ge1\). This is `core_share12_five_centre_charge_le`. It retains the whole-path singleton total \(T\); a graph charge that omits boundary singleton counts requires its own boundary calculation.

## Remaining global dependencies

This closes the identification of the local share quantity with the global budget. It does not construct the finite-graph walk of an arbitrary snake. A new global numerical bound still requires:

1. Mapping every arbitrary snake window into the exact direction, count and history states used by the chosen graph.
2. Proving every retained count exclusion and share lookup used by that graph, including reversal and coordinate relabelling where required. Bounds on the same centres must be combined by their maximum.
3. Matching the actual graph edge charges to the path budget and handling omitted boundary centres. The generic overlap multiplicity of five-centre windows is now checked in `FiveCentreOverlap`; its instantiation for the graph's window indexing remains part of this matching step.
4. Applying the verified potential to that walk with its endpoint correction and matching the exact graph and potential data versions.

The checked interval is unchanged. This bridge supports using the new local share inequalities in that eventual assembly; it supplies no new global integer upper bound by itself.
