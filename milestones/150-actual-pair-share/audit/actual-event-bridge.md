# Actual low-pair allowance for the conditional 234 comparison

This is a source review and an uncompiled proof outline. No solver, Lean process, graph search, or Git operation was used. Only this note was written. The proposed local share bounds remain hypotheses.

The direct error allowance is mathematically sound. Retain the original conditional graph weights, including floor 16 on 012032. If every fitting actual 012032 window has five-centre share at least 15, and has share at least 16 whenever its actual second and fourth internal counts sum to at least 10, then the existing occurrence theorem permits total error at most 24. The original slope 496 and potential range 602 consequently still imply at most 234 edges. The remaining margin is 6.

## Local hypothesis and precise indices

Write the five-centre integer share of a fitting six-transition window starting at \(t\) as

\[
H_t=\sum_{j=1}^{5}\operatorname{coreShare}_{12}(p,t+j).
\]

The two proposed hypotheses, restricted to canonical shape 012032, are

\[
H_t\ge15,\qquad
\alpha_{t+2}+\alpha_{t+4}\ge10\Longrightarrow H_t\ge16.
\]

Since the counts are natural numbers, these imply

\[
H_t+\mathbf1_{\{\alpha_{t+2}+\alpha_{t+4}\le9\}}\ge16.
\]

For a nine-transition graph window starting at \(r\), the six-transition suffix starts at \(t=r+3\). The five charged centres are \(r+4,\ldots,r+8\). The tested pair is therefore at \(r+5,r+7\). Define the temporary error \(e_r\) to be one exactly when that suffix has canonical shape 012032 and the **actual** pair sum is at most 9; otherwise it is zero. Omitting the shape condition would invalidate the available occurrence budget.

Relevant source interfaces:

- `milestones/98-concrete-weight-integration/lean/CountFreeCredits98.lean:28`: `conditionalFloor`, with the 012032 floor still 16 and the 012034 floor 18.
- The same file, line 72: `conditional_selected_bound`. Replace only its first shape branch by the proposed inequality. The other branches retain their existing local share hypotheses and can be weakened by the nonnegative \(e_r\).
- The same file, line 109: `actual_conditional_credit`. Its `direction_decode` and `actual_suffix_lookup` rewrites, followed by \(t=r+3\), give exactly the required graph-window indexing.

## Reversal does not double the occurrence budget

The existing shape selection supplies a forward or reversed canonical match. The word 012032 is canonically self-reversing: its reverse is 230210, whose canonical relabelling is 012032.

The existing identity `Snake9.WindowAutomaton.canon_canon_drop_reverse`, at `milestones/148-actual-snake-share-transfer/lean/WindowAutomatonLemmas.lean:230`, states

```lean
theorem canon_canon_drop_reverse (ds : List Nat) (n : Nat) :
    canon ((canon ds).drop n).reverse = canon (ds.drop n).reverse
```

Apply it to the reversed direction list with \(n=0\). A reverse canonical match to 012032 then implies the forward canonical match required by the occurrence theorem. This is a short finite computation plus the existing identity. It has not been compiled in this investigation.

Thus a single set of forward starts suffices. There is no separate reverse allowance of 24. If reversal is used instead, the established path reversal identities interchange the two tested counts and preserve the five-share sum; the shorter implementation is to normalize the canonical match without reversing the path.

## The error is counted once in each maximum

`milestones/98-concrete-weight-integration/lean/CombinedWeights98.lean:12` defines

```lean
def weight (floor : Nat → Nat) (q di code : Nat) : Nat :=
  120*(code % 6+1) +
    max (max (geometricCredits.getD di 0)
             (historyCredit concreteRules q di code))
        (max (conditionedCredit di code) (floor di))
```

All four credit alternatives bound the same five-share sum. The geometric/history and count-conditioned bounds remain at most \(H_{r+3}\). If the count-free floor is at most \(H_{r+3}+e_r\), the entire maximum is at most \(H_{r+3}+e_r\). The error is therefore charged once per graph start, independently of which alternative attains the maximum.

The proof of `actual_weight_bound`, line 17 in the same file, already contains the two necessary bounds `actual_geometric_history_credit` and `actual_conditioned_credit`. A companion lemma can weaken their conclusions to \(H_{r+3}+e_r\) before applying the same `max_le` structure. It yields

\[
w_r\le120\alpha_{r+8}+H_{r+3}+e_r.
\]

The entering count remains bounded using `sixCode_spec` and
\(\min(6,\alpha_{r+8})\le\alpha_{r+8}\). No exact interpretation of symbol 6 is introduced. The error depends on the two actual pair counts, even if either clipped symbol equals 6. This argument spends no additional count excess, so no further compensation from the same truncation is needed or assumed.

The existing `floor` argument depends only on the direction identifier. Consequently, the actual-window error should be an additional argument to a companion lemma; it cannot be encoded as a modified direction-only floor.

## Total error at most 24

`milestones/137-actual-block-assembly/lean/ActualCount137.lean:144` provides the required actual-snake theorem:

```lean
theorem low_pair_count_le_twenty_four {m : Nat} (p : Snake m) (S : Finset Nat)
    (hfit : ∀ r ∈ S, r+6 ≤ m)
    (hshape : ∀ r ∈ S, canon (dsOf p r 6) = [0,1,2,0,3,2])
    (hpair : ∀ r ∈ S, coreAlpha p (r+2)+coreAlpha p (r+4) ≤ 9) :
    S.card ≤ 24
```

Filter the graph starts `Finset.range (m-8)` by the event defining \(e_r\), and map the resulting finite set by \(r\mapsto r+3\). Addition by 3 is injective, every resulting start satisfies \(t+6\le m\), and the other hypotheses hold by the filter and canonical reversal argument. The resulting cardinality equals the indicator sum, giving

\[
\sum_{r=0}^{m-9}e_r\le24.
\]

This theorem requires neither length parity nor an endpoint-location premise. Its existing proof assigns each qualifying start to one of the two actual endpoints and bounds each assigned set by 12. The graph-start restriction merely selects a subset of all permitted starts.

## Unchanged global charge, with the error added once

Reuse these interfaces in `milestones/98-concrete-weight-integration/lean/GlobalCharge98.lean`:

- Line 55, `actual_entering_count_budget`: the entering singleton total omits at least 21 actual counts.
- Line 86, `actual_share_overlap`: each vertex share is used by at most five graph windows.
- Line 103, `actual_total_weight_budget`: the existing proof of the total weight estimate.

The last proof sums the local weight inequality, applies the first two statements, and uses `core_share12_charge_le`. A companion proof carries an extra summand \(\sum_r e_r\) through this calculation. The factor five applies to the **vertex shares**; it does not multiply the error attached to each graph start. The conclusion is

\[
W+4200m\le1098960+\sum_r e_r\le1098984.
\]

A suitable uncompiled statement interface is:

```lean
theorem actual_total_weight_budget_with_error
    (floor e : Nat → Nat) {m : Nat} (p : Snake m) (hm : 9 ≤ m)
    (hfloor : ∀ r, r+9 ≤ m →
      floor (directionId p r) ≤
        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum + e r)
    (he : (∑ r ∈ Finset.range (m-8), e r) ≤ 24) :
    (∑ r ∈ Finset.range (m-8),
      weight floor (actualHistory p r) (directionId p r) (sixCode p r)) +
      4200*m ≤ 1098984
```

This is a proposed declaration interface, not an existing checked theorem. The proof needs the small local maximum companion described above and otherwise follows the existing total-budget proof.

## Existing potential and exact margin

Use `milestones/105-reference-proof-closure/lean/ReferenceAssembly105.lean:43`, `actual_potential_bound`, with the **same** conditional floor, slope 496, range 602, reference union, and full graph potential. This source replaces the older broad catalogue assumptions by the exact union premise.

The relevant unchanged hypotheses are

```lean
(href : AllRefutedList referenceKeys)
(hR : ∀ s < 1601856, π s ≤ 602)
(hgraph : graphCheck (weight conditionalCredit) 496 π = true)
```

The existing `graphCheck_sound` converts the last hypothesis to the edge inequalities. `actual_potential_bound` then gives

\[
496(m-8)\le W+602.
\]

Combining with the error budget gives

\[
4696m\le1098984+8\cdot496+602
=1103554<1103560=235\cdot4696.
\]

Hence \(m\le234\). The old zero-error margin was 30; the allowance 24 leaves margin 6. The small case \(m<9\) is immediate. The existing `conditional234` at line 93 of this source is the assembly template: replace its original total-budget call, preserving its potential call.

## Remaining hypotheses and bounded implementation path

The next local probes must establish both proposed 012032 statements for arbitrary actual snakes, including the coordinate/canonical transfer. A native local refutation alone does not complete that obligation. The actual counts in the pair condition are essential.

The other conditional floors remain 012034 at 18, and 012301, 012340, 012345 at 16. Completed lower-floor entries are reused unchanged. At the inspected milestone148 checkpoint, the actual 012301 transfer is checked **conditional on its exact core contradiction**; `data/transfer-completion.json` explicitly records that remaining premise, and `data/checkpoint.json` says `unconditional_share16_complete` is false. The prepared `ShareComplete148.lean` source alone supplies no completion evidence. This review did not poll the running replay.

The exact reference-union refutations, the full graph potential check, and its range bound also remain explicit hypotheses. This construction concerns the original conditional graph used in milestones98/105. It needs none of the later144 graph deletions or their additional local premises.

The milestone149 obstruction concerns a different allowance: it credits only the coarse event with both tested symbols below 6. Its saved 28-edge walk includes 012032 rows with symbol 6 in a tested position, so the coarse event can vanish when the actual event is possible. That obstruction does not contradict the present actual-window deduction. The present proof retains the floor-16 weights and applies a globally bounded error to their interpretation along an actual snake; it does not require a new coarse graph potential.

The shortest implementation after the local premises are available is:

1. Prove the canonical self-reversal implication and the indicator sum bound from `low_pair_count_le_twenty_four`.
2. Adapt the first branch of `conditional_selected_bound` and its existing suffix lookup to obtain the floor bound with one error.
3. Add the local maximum and global-sum companion lemmas, preserving the count truncation argument.
4. Reuse `ReferenceAssembly105.actual_potential_bound` unchanged and finish the displayed integer arithmetic.

No new graph optimization, extra endpoint hypothesis, doubled reversal budget, or count-excess estimate is needed for this deduction. All newly proposed companions remain uncompiled in this note, and no new unconditional upper bound is claimed.

## Subsequent native evidence reported by the coordinating agent

After this review was completed, the coordinating agent reported an independently replayed native proof for the high-pair share-16 probe: 58,182 deductions, 5,350,080 hints and 13,655 retained input clauses. She reported that zero retained clauses use the new pair-counter premises, so the retained core may already refute the original unrestricted 012032 share cap 15. These figures and the unused-premise interpretation were not independently inspected in this investigation. The coordinating agent is auditing that stronger interpretation. Neither the proposed split local target nor unrestricted share 16 is treated as Lean-checked here. If the stronger original target is established, the existing zero-error assembly applies and this allowance remains an optional weaker sufficient condition.
