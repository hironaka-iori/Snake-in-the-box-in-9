import Context101Group02

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.Context101
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.HistoryShare94
open Snake9.Guards79 Snake9.Weights98 Snake9.CountFree98

theorem history_99_37 (code : Nat) :
    emittedCredit [rule000] code =
      if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18 := by
  by_cases h1 : digit code 1 ≤ 2 <;> by_cases h2 : digit code 2 ≤ 2 <;>
    simp [emittedCredit, rule000, numericCapsTest, h1, h2]

theorem completed_simplified_99_37 (code : Nat) :
    weight completedCredit 37 99 code =
      120*(code%6+1)+max
        (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18)
        (if code%7776 = 3221 then 96 else 0) := by
  rw [completed_99_37, history_99_37]
  split_ifs <;> norm_num

theorem conditional_simplified_99_37 (code : Nat) :
    weight conditionalCredit 37 99 code =
      120*(code%6+1)+max
        (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18)
        (if code%7776 = 3221 then 96 else 0) := by
  rw [conditional_99_37, history_99_37]
  split_ifs <;> norm_num

theorem profiles_equal_99_37 (code : Nat) :
    weight completedCredit 37 99 code = weight conditionalCredit 37 99 code := by
  rw [completed_simplified_99_37, conditional_simplified_99_37]

#print axioms history_99_37
#print axioms completed_simplified_99_37
#print axioms conditional_simplified_99_37
#print axioms profiles_equal_99_37
end Snake9.Context101
