import HistoryShareAssembly

/-!
Reverse inclusion for the saved history-share covers. Together with the
coverage theorem this identifies each listed variant set exactly with the
canonical eleven-direction words satisfying the stated compatibility tests.
It supplies no geometric share bound or realization by a complete snake.
This source awaits compilation.
-/

namespace Snake9.HistoryShare94
open Snake9.WindowAutomaton Snake9.Direction77 Snake9.History84

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The exact hypotheses used by share_cover_mem, encoded as one Boolean test.
The signature length is separately fixed by membership in savedShareRules. -/
def variantFits (sig cs : List Nat) : Bool :=
  decide (cs.length = 11) &&
    (decide (cs.take 9 = extensions.getD (sig.getD 0 0) []) &&
      (cs.all (fun d => decide (d < 9)) &&
        (isRGS cs 0 && (inducedPattern cs && realizes sig cs))))

/-- Check every listed word of every exact saved pair. -/
def savedVariantsCheck : Bool :=
  savedShareRules.all fun rule => rule.2.all (variantFits rule.1)

/-- Concrete finite validity check of the supplied variant lists. -/
theorem saved_variants_checked : savedVariantsCheck = true := by
  decide +kernel

/-- Every listed variant satisfies the complete compatibility predicate. -/
theorem saved_variant_fits (rule : List Nat × List (List Nat))
    (hrule : rule ∈ savedShareRules) (cs : List Nat) (hcs : cs ∈ rule.2) :
    variantFits rule.1 cs = true := by
  have h := List.all_eq_true.mp saved_variants_checked rule hrule
  exact List.all_eq_true.mp h cs hcs

/-- Exact compatible-word set for any saved rule. This is a statement about
canonical local direction words, not extension to a complete snake. -/
theorem saved_variant_iff_fits (rule : List Nat × List (List Nat))
    (hrule : rule ∈ savedShareRules) (cs : List Nat) :
    cs ∈ rule.2 ↔ variantFits rule.1 cs = true := by
  constructor
  · exact saved_variant_fits rule hrule cs
  · intro hfits
    have hspec : cs.length = 11 ∧
        cs.take 9 = extensions.getD (rule.1.getD 0 0) [] ∧
        (∀ d ∈ cs, d < 9) ∧ isRGS cs 0 = true ∧
        inducedPattern cs = true ∧ realizes rule.1 cs = true := by
      simpa only [variantFits, Bool.and_eq_true_iff, decide_eq_true_eq,
        List.all_eq_true] using hfits
    obtain ⟨hlen,hprefix,hsmall,hrgs,hind,hreal⟩ := hspec
    exact share_cover_mem rule.1 rule.2 cs (saved_share_rule_spec rule hrule).2
      hlen hprefix hsmall hrgs hind hreal

#print axioms saved_variants_checked
#print axioms saved_variant_fits
#print axioms saved_variant_iff_fits

end Snake9.HistoryShare94
