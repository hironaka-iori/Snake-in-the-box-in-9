import GuardTransfer
import CycleExclusion471
import CycleExclusion472
import CycleExclusion473
import CycleExclusion483
import CycleExclusion4901
import CycleExclusion4902
import CycleExclusion4903
import CycleExclusion4904
import CycleExclusion4905
import CycleExclusion4906
import CycleExclusion4907
import CycleExclusion4908
import CycleExclusion4909
import CycleExclusion4910
import CycleExclusion4911
import CycleExclusion4912
import CycleExclusion4913
import CycleExclusion4914
import CycleExclusion4915
import CycleExclusion4916
import CycleExclusion4917
import CycleExclusion4918
import CycleExclusion4919
import CycleExclusion4920
import CycleExclusion4921
import CycleExclusion4922
import CycleExclusion4923
import CycleExclusion4924
import CycleExclusion4925
import CycleExclusion4926
import CycleExclusion4927
import CycleExclusion4928
import CycleExclusion4929
import CycleExclusion4930
import CycleExclusion4931
import CycleExclusion4932
import CycleExclusion4933

namespace Snake9.ShortRules81
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79
set_option maxHeartbeats 2000000

theorem safe471 : rawSafe [0,1,2,3,0,4] (.caps [(4,1)]) := by
  apply caps_from_refuted [0,1,2,3,0,4] [(4,1)] [(0,21),(0,21),(0,21),(0,1),(0,21)] (by decide) CycleWindow471.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe472 : rawSafe [0,1,2,3,0,4,1] (.caps [(1,1)]) := by
  apply caps_from_refuted [0,1,2,3,0,4,1] [(1,1)] [(0,1),(0,21),(0,21),(0,21),(0,21),(0,21)] (by decide) CycleWindow472.refuted
  intro i hi
  change i < 6 at hi
  interval_cases i <;> simp

theorem safe473 : rawSafe [0,1,2,3,0,2,4,3] (.caps [(7,1)]) := by
  apply caps_from_refuted [0,1,2,3,0,2,4,3] [(7,1)] [(0,21),(0,21),(0,21),(0,21),(0,21),(0,21),(0,1)] (by decide) CycleWindow473.refuted
  intro i hi
  change i < 7 at hi
  interval_cases i <;> simp

theorem safe483 : rawSafe [0,1,2,3,4,2] (.caps [(1,3),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,2] [(1,3),(5,2)] [(0,3),(0,21),(0,21),(0,21),(0,2)] (by decide) CycleWindow483.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4901 : rawSafe [0,1,2,0] (.caps [(1,2),(3,2)]) := by
  apply caps_from_refuted [0,1,2,0] [(1,2),(3,2)] [(0,2),(0,21),(0,2)] (by decide) CycleWindow4901.refuted
  intro i hi
  change i < 3 at hi
  interval_cases i <;> simp

theorem safe4902 : rawSafe [0,1,2,0,3,1] (.caps [(1,2),(4,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,1] [(1,2),(4,2)] [(0,2),(0,21),(0,21),(0,2),(0,21)] (by decide) CycleWindow4902.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4903 : rawSafe [0,1,2,0,3,1] (.caps [(1,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,0,3,1] [(1,2),(5,3)] [(0,2),(0,21),(0,21),(0,21),(0,3)] (by decide) CycleWindow4903.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4904 : rawSafe [0,1,2,0,3,1] (.caps [(1,3),(5,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,1] [(1,3),(5,2)] [(0,3),(0,21),(0,21),(0,21),(0,2)] (by decide) CycleWindow4904.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4905 : rawSafe [0,1,2,0,3,2] (.caps [(1,3),(3,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,2] [(1,3),(3,2)] [(0,3),(0,21),(0,2),(0,21),(0,21)] (by decide) CycleWindow4905.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4906 : rawSafe [0,1,2,0,3,2] (.caps [(1,2),(4,3)]) := by
  apply caps_from_refuted [0,1,2,0,3,2] [(1,2),(4,3)] [(0,2),(0,21),(0,21),(0,3),(0,21)] (by decide) CycleWindow4906.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4907 : rawSafe [0,1,2,0,3,2] (.caps [(2,3),(4,3)]) := by
  apply caps_from_refuted [0,1,2,0,3,2] [(2,3),(4,3)] [(0,21),(0,3),(0,21),(0,3),(0,21)] (by decide) CycleWindow4907.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4908 : rawSafe [0,1,2,0,3,2] (.caps [(2,3),(5,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,2] [(2,3),(5,2)] [(0,21),(0,3),(0,21),(0,21),(0,2)] (by decide) CycleWindow4908.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4909 : rawSafe [0,1,2,0,3,2] (.caps [(3,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,0,3,2] [(3,2),(5,3)] [(0,21),(0,21),(0,2),(0,21),(0,3)] (by decide) CycleWindow4909.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4910 : rawSafe [0,1,2,0,3,4] (.caps [(1,3),(3,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,4] [(1,3),(3,2)] [(0,3),(0,21),(0,2),(0,21),(0,21)] (by decide) CycleWindow4910.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4911 : rawSafe [0,1,2,0,3,4] (.caps [(1,2),(4,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,4] [(1,2),(4,2)] [(0,2),(0,21),(0,21),(0,2),(0,21)] (by decide) CycleWindow4911.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4912 : rawSafe [0,1,2,0,3,4] (.caps [(1,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,0,3,4] [(1,2),(5,3)] [(0,2),(0,21),(0,21),(0,21),(0,3)] (by decide) CycleWindow4912.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4913 : rawSafe [0,1,2,0,3,4] (.caps [(2,2),(4,2)]) := by
  apply caps_from_refuted [0,1,2,0,3,4] [(2,2),(4,2)] [(0,21),(0,2),(0,21),(0,2),(0,21)] (by decide) CycleWindow4913.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4914 : rawSafe [0,1,2,3,0,1] (.caps [(1,2),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,0,1] [(1,2),(5,2)] [(0,2),(0,21),(0,21),(0,21),(0,2)] (by decide) CycleWindow4914.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4915 : rawSafe [0,1,2,3,0,4] (.caps [(1,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,3,0,4] [(1,2),(5,3)] [(0,2),(0,21),(0,21),(0,21),(0,3)] (by decide) CycleWindow4915.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4916 : rawSafe [0,1,2,3,0,4] (.caps [(1,3),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,0,4] [(1,3),(5,2)] [(0,3),(0,21),(0,21),(0,21),(0,2)] (by decide) CycleWindow4916.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4917 : rawSafe [0,1,2,3,0,4] (.caps [(4,2),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,0,4] [(4,2),(5,2)] [(0,21),(0,21),(0,21),(0,2),(0,2)] (by decide) CycleWindow4917.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4918 : rawSafe [0,1,2,3,1,0] (.caps [(1,2),(2,2)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(1,2),(2,2)] [(0,2),(0,2),(0,21),(0,21),(0,21)] (by decide) CycleWindow4918.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4919 : rawSafe [0,1,2,3,1,0] (.caps [(1,3),(3,2)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(1,3),(3,2)] [(0,3),(0,21),(0,2),(0,21),(0,21)] (by decide) CycleWindow4919.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4920 : rawSafe [0,1,2,3,1,0] (.caps [(1,2),(4,2)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(1,2),(4,2)] [(0,2),(0,21),(0,21),(0,2),(0,21)] (by decide) CycleWindow4920.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4921 : rawSafe [0,1,2,3,1,0] (.caps [(2,2),(4,3)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(2,2),(4,3)] [(0,21),(0,2),(0,21),(0,3),(0,21)] (by decide) CycleWindow4921.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4922 : rawSafe [0,1,2,3,1,0] (.caps [(2,3),(4,2)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(2,3),(4,2)] [(0,21),(0,3),(0,21),(0,2),(0,21)] (by decide) CycleWindow4922.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4923 : rawSafe [0,1,2,3,1,0] (.caps [(2,2),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(2,2),(5,2)] [(0,21),(0,2),(0,21),(0,21),(0,2)] (by decide) CycleWindow4923.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4924 : rawSafe [0,1,2,3,1,0] (.caps [(3,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(3,2),(5,3)] [(0,21),(0,21),(0,2),(0,21),(0,3)] (by decide) CycleWindow4924.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4925 : rawSafe [0,1,2,3,1,0] (.caps [(4,2),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,1,0] [(4,2),(5,2)] [(0,21),(0,21),(0,21),(0,2),(0,2)] (by decide) CycleWindow4925.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4926 : rawSafe [0,1,2,3,4,0] (.caps [(1,2),(2,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,0] [(1,2),(2,2)] [(0,2),(0,2),(0,21),(0,21),(0,21)] (by decide) CycleWindow4926.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4927 : rawSafe [0,1,2,3,4,0] (.caps [(1,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,3,4,0] [(1,2),(5,3)] [(0,2),(0,21),(0,21),(0,21),(0,3)] (by decide) CycleWindow4927.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4928 : rawSafe [0,1,2,3,4,0] (.caps [(1,3),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,0] [(1,3),(5,2)] [(0,3),(0,21),(0,21),(0,21),(0,2)] (by decide) CycleWindow4928.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4929 : rawSafe [0,1,2,3,4,0] (.caps [(4,2),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,0] [(4,2),(5,2)] [(0,21),(0,21),(0,21),(0,2),(0,2)] (by decide) CycleWindow4929.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4930 : rawSafe [0,1,2,3,4,5] (.caps [(1,2),(2,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,5] [(1,2),(2,2)] [(0,2),(0,2),(0,21),(0,21),(0,21)] (by decide) CycleWindow4930.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4931 : rawSafe [0,1,2,3,4,5] (.caps [(1,2),(5,3)]) := by
  apply caps_from_refuted [0,1,2,3,4,5] [(1,2),(5,3)] [(0,2),(0,21),(0,21),(0,21),(0,3)] (by decide) CycleWindow4931.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4932 : rawSafe [0,1,2,3,4,5] (.caps [(1,3),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,5] [(1,3),(5,2)] [(0,3),(0,21),(0,21),(0,21),(0,2)] (by decide) CycleWindow4932.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

theorem safe4933 : rawSafe [0,1,2,3,4,5] (.caps [(4,2),(5,2)]) := by
  apply caps_from_refuted [0,1,2,3,4,5] [(4,2),(5,2)] [(0,21),(0,21),(0,21),(0,2),(0,2)] (by decide) CycleWindow4933.refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp

def capRules : List (List Nat × CountTest) := [
([0,1,2,3,0,4], .caps [(4,1)]),
([0,1,2,3,0,4,1], .caps [(1,1)]),
([0,1,2,3,0,2,4,3], .caps [(7,1)]),
([0,1,2,3,4,2], .caps [(1,3),(5,2)]),
([0,1,2,0], .caps [(1,2),(3,2)]),
([0,1,2,0,3,1], .caps [(1,2),(4,2)]),
([0,1,2,0,3,1], .caps [(1,2),(5,3)]),
([0,1,2,0,3,1], .caps [(1,3),(5,2)]),
([0,1,2,0,3,2], .caps [(1,3),(3,2)]),
([0,1,2,0,3,2], .caps [(1,2),(4,3)]),
([0,1,2,0,3,2], .caps [(2,3),(4,3)]),
([0,1,2,0,3,2], .caps [(2,3),(5,2)]),
([0,1,2,0,3,2], .caps [(3,2),(5,3)]),
([0,1,2,0,3,4], .caps [(1,3),(3,2)]),
([0,1,2,0,3,4], .caps [(1,2),(4,2)]),
([0,1,2,0,3,4], .caps [(1,2),(5,3)]),
([0,1,2,0,3,4], .caps [(2,2),(4,2)]),
([0,1,2,3,0,1], .caps [(1,2),(5,2)]),
([0,1,2,3,0,4], .caps [(1,2),(5,3)]),
([0,1,2,3,0,4], .caps [(1,3),(5,2)]),
([0,1,2,3,0,4], .caps [(4,2),(5,2)]),
([0,1,2,3,1,0], .caps [(1,2),(2,2)]),
([0,1,2,3,1,0], .caps [(1,3),(3,2)]),
([0,1,2,3,1,0], .caps [(1,2),(4,2)]),
([0,1,2,3,1,0], .caps [(2,2),(4,3)]),
([0,1,2,3,1,0], .caps [(2,3),(4,2)]),
([0,1,2,3,1,0], .caps [(2,2),(5,2)]),
([0,1,2,3,1,0], .caps [(3,2),(5,3)]),
([0,1,2,3,1,0], .caps [(4,2),(5,2)]),
([0,1,2,3,4,0], .caps [(1,2),(2,2)]),
([0,1,2,3,4,0], .caps [(1,2),(5,3)]),
([0,1,2,3,4,0], .caps [(1,3),(5,2)]),
([0,1,2,3,4,0], .caps [(4,2),(5,2)]),
([0,1,2,3,4,5], .caps [(1,2),(2,2)]),
([0,1,2,3,4,5], .caps [(1,2),(5,3)]),
([0,1,2,3,4,5], .caps [(1,3),(5,2)]),
([0,1,2,3,4,5], .caps [(4,2),(5,2)])
]

theorem cap_catalogue : ∀ rule ∈ capRules, rawSafe rule.1 rule.2 ∧
    smallCaps rule.2 ∧ internalPositions rule.2 rule.1.length := by
  intro rule h
  simp only [capRules, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨safe471, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe472, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe473, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe483, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4901, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4902, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4903, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4904, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4905, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4906, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4907, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4908, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4909, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4910, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4911, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4912, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4913, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4914, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4915, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4916, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4917, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4918, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4919, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4920, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4921, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4922, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4923, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4924, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4925, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4926, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4927, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4928, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4929, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4930, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4931, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4932, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩
  · exact ⟨safe4933, by simp [smallCaps], by simp [internalPositions, CountTest.positions]⟩

#print axioms safe471
#print axioms safe472
#print axioms safe473
#print axioms safe483
#print axioms safe4901
#print axioms safe4902
#print axioms safe4903
#print axioms safe4904
#print axioms safe4905
#print axioms safe4906
#print axioms safe4907
#print axioms safe4908
#print axioms safe4909
#print axioms safe4910
#print axioms safe4911
#print axioms safe4912
#print axioms safe4913
#print axioms safe4914
#print axioms safe4915
#print axioms safe4916
#print axioms safe4917
#print axioms safe4918
#print axioms safe4919
#print axioms safe4920
#print axioms safe4921
#print axioms safe4922
#print axioms safe4923
#print axioms safe4924
#print axioms safe4925
#print axioms safe4926
#print axioms safe4927
#print axioms safe4928
#print axioms safe4929
#print axioms safe4930
#print axioms safe4931
#print axioms safe4932
#print axioms safe4933
#print axioms cap_catalogue
end Snake9.ShortRules81
