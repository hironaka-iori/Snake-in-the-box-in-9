import WeightSpecialization100

/-! Exact weight evaluation after a context's emitting rules and fixed
lookups have been identified. Concrete context certificates are separate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.ContextWeights101
open Snake9.HistoryCredit95 Snake9.HistoryShare94 Snake9.ConcreteCatalogue95
open Snake9.WeightSpecialization100 Snake9.Weights98
open Snake9.GeometricCredit97 Snake9.Conditioned98

/-- Evaluate an already-emitting list, preserving every geometric and
cap-conditioned alternative and the original maximum operation. -/
def emittedCredit : List Rule → Nat → Nat
  | [], _ => 0
  | rule :: rest, code =>
      max
        (max rule.geometric
          (if numericCapsTest code rule.caps = true then rule.strong else 0))
        (emittedCredit rest code)

theorem historyCredit_eq_emitted (rules : List Rule) (q di code : Nat)
    (hemit : ∀ rule ∈ rules,
      rule.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di]) :
    historyCredit rules q di code = emittedCredit rules code := by
  revert hemit
  induction rules with
  | nil =>
      intro _
      rfl
  | cons rule rest ih =>
      intro hemit
      have hr : rule.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di] :=
        hemit rule (by simp)
      have hrest : ∀ other ∈ rest,
          other.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di] := by
        intro other hother
        exact hemit other (List.mem_cons_of_mem rule hother)
      simp only [historyCredit, emittedCredit, contribution, if_pos hr, ih hrest]

/-- The selected list is exactly the original filter, including order and
multiplicity. No range, geometric-validity or refutation premise is needed
for this equality of executable evaluators. -/
theorem historyCredit_eq_selected (selected : List Rule) (q di code : Nat)
    (hselected : selected = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di]))) :
    historyCredit concreteRules q di code = emittedCredit selected code := by
  rw [historyCredit_filter_emitting concreteRules q di code, ← hselected]
  apply historyCredit_eq_emitted
  intro rule hrule
  have hfiltered : rule ∈ concreteRules.filter (fun other =>
      decide (other.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di])) := by
    rw [← hselected]
    exact hrule
  exact of_decide_eq_true (List.mem_filter.mp hfiltered).2

/-- Specialize fixed context data once; only cap tests and the supplied
conditioned-credit expression depend on the count code afterward. -/
theorem weight_eq_context (floor : Nat → Nat) (q di : Nat)
    (selected : List Rule) (G F : Nat) (C : Nat → Nat)
    (hselected : selected = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD q [] ++ [di])))
    (hG : G = geometricCredits.getD di 0)
    (hF : F = floor di)
    (hC : ∀ code, conditionedCredit di code = C code)
    (code : Nat) :
    weight floor q di code =
      120*(code%6+1) +
        max (max G (emittedCredit selected code)) (max (C code) F) := by
  unfold weight
  rw [historyCredit_eq_selected selected q di code hselected, ← hG, ← hF, hC code]

#print axioms historyCredit_eq_emitted
#print axioms historyCredit_eq_selected
#print axioms weight_eq_context
end Snake9.ContextWeights101
