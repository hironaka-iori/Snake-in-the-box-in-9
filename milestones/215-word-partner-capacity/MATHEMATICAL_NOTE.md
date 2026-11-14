# Round 215: actual-word capacity and partner capacity

The hypothesis was that competition for actual word labels supplies restrictions missed by partner counting alone. The resulting preservation theorem is checked in Lean and used in a separate native search. This is established finite distinct-value reasoning applied to the saved snake geometry; no novelty or speed improvement is claimed.

## Mathematical deduction

Let F be one of the four chosen/outside parity families in the retained(0,6) construction. The actual indexed induced-path condition implies that the assigned words within F are pairwise distinct. Let J be a subset of F and let U contain every current domain of every member of J. Any fitting assignment injects J into U. Therefore

\[
|J|\le |U|.
\]

If equality holds, the assigned words on J occupy all of U. Each other member of F has a different assigned word, so it must avoid U. Deleting U from that member's domain preserves the same complete assignment and hence all path conditions.

This argument requires current-domain fitting, the family/subset premises and the stated containment/cardinality. It needs neither normalization at zero nor a raw-value bound, a fixed parity-pool size, or saturation of all32 words. Raw integer distinctness follows from the path even when the six-bit decoder is not globally injective: equal raw values always decode equally, which contradicts the derived geometric distinctness. The native six-bit masks still have their separate interpretation requirements.

One new module, PathWordCapacity215, passes with three theorem-dependency reports, using only propext, Classical.choice and Quot.sound. It obtains the four literal families' distinctness from round213, then composes the deficient-pool and tight-filter arguments from round211. Complete arbitrary-input normalization, native domain-mask interpretation and traversal certification remain separate.

## Native use

The new engine applies distinct-word capacity separately to each chosen and outside family, then invokes the existing tight-partner rule. A matching proposes subsets. Every failed matching is followed by an actual deficient-union count. Before deleting a tight union, the current domains are recomputed and their union cardinality checked. Earlier deletions can make the stored matching stale, but that matching only proposes a subset; the current union justifies the deduction. Filtering never crosses between the chosen and outside families, since those families can legitimately share words.

A bounded independent source review found no defect under these premises. The source review, finite Lean theorem and saved-transition audit do not constitute kernel certification of the C execution or full search. No software tests were created or run.

The transfer preserves all1448 prior files and all13 unfinished domain vectors. It changes only engine pins and the explicit transfer record. Older source snapshots are preserved; transfer214-state.json and transfer214-initial-state.json identify the newly imported baseline. The frozen round214 state is unchanged.

The continuation accepts 500 new jobs, visits 2,650,260 additional nodes and reports 296.922 solver seconds. New job outcomes are {'EXHAUSTED': 437, 'LIMIT': 63}. Actual-word capacity records 29,311,693 removal operations and 841,841 contradiction returns. Tight-partner capacity records 239,872 removal operations and 3,910 contradiction returns. These are repeated branch operations, not counts of globally distinct excluded assignments.

The independently audited saved chain remains OPEN at 740 total jobs, 5 pending regions and 4,451,277 cumulative nodes. Final state SHA-256: 1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb. No new parent class, longer snake or complete coordinate-case exclusion was obtained. Only retained[1,4] is exhausted among the28 six-coordinate cases;27 remain unresolved. Other open cases remain frozen at their prior milestones.

## Research conclusion and next step

Continue the five saved regions with the combined word/partner engine, while investigating a restriction involving both parities. A useful candidate is joint support for three consecutive free-word groups: an allowed outer pair needs a common middle neighbour in its domain, and the two outer words must also satisfy their own binary relation. All three conditions must hold together; separate support at the middle alone already follows from binary propagation. First compare joint pair/value support with the complete current propagation on frozen domains; derive the geometric implication and check it in Lean before using any new rejection rule. This is an unproved improvement proposal, not a claim of new pruning. Do not prioritize maximal mixed-family Hall propagation solely on the present snapshot: its35 apparent extra deletions disappear after the existing four-family Hall and binary rules reach closure. Twelve inherited regions then admit no additional mixed-family deduction, and the thirteenth is already deficient under the existing rules. The four maximal families per parity remain a valid structural observation, with implementation benefit unestablished.

The recorded interval remains191<=a(9)<=233. The contributor233 theorem is unconditional, with its saved assembly and axiom audit recorded in round213; independent full rebuilding remains pending. No own numerical bound changed. The conjectured196 remains unresolved. The primary-source check saved in logs/parent-literature-check.md found no accessible classification establishing uniqueness of the98-edge parent; absence of such a catalogue in that check is not evidence of uniqueness.

The goal remains ACTIVE. Ordinary progress warrants continuation. A substantial result or prolonged lack of progress in the user's and this agent's own work may trigger the authorized pause; contributor work alone cannot. No email was sent because no sending connector is available. Both existing manuscripts compile, preserve all three authors and local hyperlink settings, and have exact paper mirrors. Last full-paper review210; next scheduled220.
