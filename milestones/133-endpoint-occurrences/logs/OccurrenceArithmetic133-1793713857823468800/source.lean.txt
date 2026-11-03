import Mathlib.Tactic

namespace Snake9.OccurrenceArithmetic133

set_option maxHeartbeats 2000000

theorem exceptional_parameters (W a k t δ : Int)
    (ha : 1 ≤ a) (ha7 : a ≤ 7) (hak : a ≤ k) (ht : 0 ≤ t)
    (hfirst : W ≤ 7*a-a*(a-1)/2-t-2*k+δ)
    (hsecond : W ≤ k*(5-a+t)-t+1+δ)
    (hlarge : 12+δ ≤ W) :
    a=5 ∧ k=5 ∧ t=3 ∧ W=12+δ := by
  have hkhi : k ≤ 8 := by
    interval_cases a <;> norm_num at hfirst <;> omega
  have hklo : 1 ≤ k := by omega
  interval_cases a <;> interval_cases k <;> norm_num at * <;> omega

theorem occurrence_le_eleven (W a k t δ : Int)
    (ha : 1 ≤ a) (ha7 : a ≤ 7) (hak : a ≤ k) (ht : 0 ≤ t)
    (hfirst : W ≤ 7*a-a*(a-1)/2-t-2*k+δ)
    (hsecond : W ≤ k*(5-a+t)-t+1+δ)
    (hextra : a=5 → k=5 → t=3 → W+3*k ≤ 6*a-4+δ) :
    W ≤ 11+δ := by
  by_contra hn
  have hlarge : 12+δ ≤ W := by omega
  obtain ⟨ha5,hk5,ht3,hW⟩ := exceptional_parameters W a k t δ
    ha ha7 hak ht hfirst hsecond hlarge
  have hbound := hextra ha5 hk5 ht3
  norm_num [ha5,hk5] at hbound
  omega

#print axioms exceptional_parameters
#print axioms occurrence_le_eleven
end Snake9.OccurrenceArithmetic133
