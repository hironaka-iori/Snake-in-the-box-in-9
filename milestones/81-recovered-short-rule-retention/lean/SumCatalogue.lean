import GuardTransfer
import SumWindow481
import SumWindow482
import SumWindow501

namespace Snake9.ShortRules81
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79
set_option maxHeartbeats 2000000

theorem safe481 : rawSafe [0,1,2,3,0,1] (.sum [1,5] 4) := by
  intro m p r hr hshape hbad
  change r+6 ≤ m at hr
  change canon (dsOf p r 6) = [0,1,2,3,0,1] at hshape
  obtain ⟨P,hP⟩ := canonical_permutation p r 6 hr
  have hlo := JointIntervening481.sum_in_snake p P r hr (by
    intro j hj
    have h := hP j hj
    rw [hshape] at h
    exact h)
  change ([1,5].map (fun j => coreAlpha p (r+j))).sum ≤ 4 at hbad
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hbad
  omega

theorem safe482 : rawSafe [0,1,2,3,0,4,1,0] (.sum [4,7] 5) := by
  intro m p r hr hshape hbad
  change r+8 ≤ m at hr
  change canon (dsOf p r 8) = [0,1,2,3,0,4,1,0] at hshape
  obtain ⟨P,hP⟩ := canonical_permutation p r 8 hr
  have hlo := JointIntervening482.sum_in_snake p P r hr (by
    intro j hj
    have h := hP j hj
    rw [hshape] at h
    exact h)
  change ([4,7].map (fun j => coreAlpha p (r+j))).sum ≤ 5 at hbad
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hbad
  omega

theorem safe501 : rawSafe [0,1,2,3,4,0] (.sum [1,4,5] 12) := by
  intro m p r hr hshape hbad
  change r+6 ≤ m at hr
  change canon (dsOf p r 6) = [0,1,2,3,4,0] at hshape
  obtain ⟨P,hP⟩ := canonical_permutation p r 6 hr
  have hlo := JointIntervening501.sum_in_snake p P r hr (by
    intro j hj
    have h := hP j hj
    rw [hshape] at h
    exact h)
  change ([1,4,5].map (fun j => coreAlpha p (r+j))).sum ≤ 12 at hbad
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hbad
  omega

def sumRules : List (List Nat × CountTest) := [
([0,1,2,3,0,1], .sum [1,5] 4),
([0,1,2,3,0,4,1,0], .sum [4,7] 5),
([0,1,2,3,4,0], .sum [1,4,5] 12)
]

theorem sum_catalogue : ∀ rule ∈ sumRules, rawSafe rule.1 rule.2 ∧
    smallCaps rule.2 ∧ internalPositions rule.2 rule.1.length := by
  intro rule h
  simp only [sumRules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact ⟨safe481, trivial, by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe482, trivial, by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe501, trivial, by simp [internalPositions, CountTest.positions]⟩

#print axioms safe481
#print axioms safe482
#print axioms safe501
#print axioms sum_catalogue
end Snake9.ShortRules81
