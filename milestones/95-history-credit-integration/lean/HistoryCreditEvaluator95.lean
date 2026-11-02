import HistoryShareCaps

/-!
Generic maximum-based history-share evaluator. Every concrete rule requires
its cover, signature-length, unsaturated-cap and per-word geometric premises.
This source awaits compilation.
-/

namespace Snake9.HistoryCredit95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94

set_option maxHeartbeats 2000000

structure Rule where
  sig : List Nat
  words : List (List Nat)
  caps : List (Nat × Nat)
  geometric : Nat
  strong : Nat

/-- All semantic obligations for a rule. Ambiguous words require individual
proofs; numeric emission alone establishes no share bound. -/
def RuleValid (rule : Rule) : Prop :=
  rule.sig.length = 3 ∧
    shareCoverTable rule.sig rule.words = true ∧
    (∀ kc ∈ rule.caps, kc.1 < 6 ∧ kc.2 < 6) ∧
    (∀ cs ∈ rule.words, WordShareBound cs rule.geometric) ∧
    (∀ cs ∈ rule.words, WordCappedShareBound cs rule.caps rule.strong)

/-- The stronger cap-dependent bound is an alternative for the same share
sum. Both it and the geometric bound are combined by maximum. -/
def contribution (rule : Rule) (q di code : Nat) : Nat :=
  if rule.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di] then
    max rule.geometric
      (if numericCapsTest code rule.caps = true then rule.strong else 0)
  else 0

/-- Maximum over the list, with zero for an empty rule list. -/
def historyCredit : List Rule → Nat → Nat → Nat → Nat
  | [], _, _, _ => 0
  | rule :: rest, q, di, code =>
      max (contribution rule q di code) (historyCredit rest q di code)

theorem actual_contribution_le {m : Nat} (p : Snake m) (r : Nat)
    (rule : Rule) (hr : r+9 ≤ m) (hvalid : RuleValid rule) :
    contribution rule (actualHistory p r) (directionId p r) (sixCode p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  obtain ⟨hlen,hcover,hcaps,hgeom,hstrong⟩ := hvalid
  by_cases hemit : rule.sig <:+
      Snake9.History75.prefixes.getD (actualHistory p r) [] ++ [directionId p r]
  · simp only [contribution, if_pos hemit]
    apply max_le
    · exact emitted_five_centre_share p r rule.sig rule.words rule.geometric
        hr hlen hcover hemit hgeom
    · by_cases hhit : numericCapsTest (sixCode p r) rule.caps = true
      · simp only [if_pos hhit]
        exact emitted_capped_share_of_numeric_test p r rule.sig rule.words
          rule.caps rule.strong hr hlen hcover hemit hcaps hhit hstrong
      · simp only [if_neg hhit]
        exact Nat.zero_le _
  · simp only [contribution, if_neg hemit]
    exact Nat.zero_le _

/-- A maximum of contributions bounded by one common sum remains bounded by
that sum. Rules may overlap and may occur more than once. -/
theorem history_credit_le_of_each (rules : List Rule) (q di code B : Nat) :
    (∀ rule ∈ rules, contribution rule q di code ≤ B) →
    historyCredit rules q di code ≤ B := by
  induction rules with
  | nil =>
      intro _
      exact Nat.zero_le _
  | cons rule rest ih =>
      intro h
      change max (contribution rule q di code) (historyCredit rest q di code) ≤ B
      apply max_le
      · exact h rule (by simp)
      · apply ih
        intro other hother
        exact h other (List.mem_cons_of_mem rule hother)

/-- Actual five-centre bound for the complete finite evaluator. All supplied
rules must satisfy their own exact semantic obligations. -/
theorem actual_history_credit_le {m : Nat} (p : Snake m) (r : Nat)
    (rules : List Rule) (hr : r+9 ≤ m)
    (hvalid : ∀ rule ∈ rules, RuleValid rule) :
    historyCredit rules (actualHistory p r) (directionId p r) (sixCode p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  apply history_credit_le_of_each
  intro rule hrule
  exact actual_contribution_le p r rule hr (hvalid rule hrule)

#print axioms actual_contribution_le
#print axioms history_credit_le_of_each
#print axioms actual_history_credit_le

end Snake9.HistoryCredit95
