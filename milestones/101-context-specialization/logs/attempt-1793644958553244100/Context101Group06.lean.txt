import Direction101Group03
import Direction101Group04

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_231_3 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 3 [] ++ [231])) := by rfl

theorem source_231_3 (code : Nat) :
    edgeSource 3 231 code = 1041984+code/6 := by rfl

theorem target_231_3 (code : Nat) :
    edgeTarget 3 231 code = 186624+code%7776 := by rfl

theorem block_231_3 :
    savedBlockClass (75*231+3) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_231_3 (code : Nat) :
    weight completedCredit 3 231 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 3 231 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_231_3 direction_231.1
    direction_231.2.1 conditioned_231 code

theorem conditional_231_3 (code : Nat) :
    weight conditionalCredit 3 231 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 3 231 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_231_3 direction_231.1
    direction_231.2.2 conditioned_231 code
#print axioms selected_231_3
#print axioms source_231_3
#print axioms target_231_3
#print axioms block_231_3
#print axioms completed_231_3
#print axioms conditional_231_3

theorem selected_232_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [232])) := by rfl

theorem source_232_0 (code : Nat) :
    edgeSource 0 232 code = 513216+code/6 := by rfl

theorem target_232_0 (code : Nat) :
    edgeTarget 0 232 code = 155520+code%7776 := by rfl

theorem block_232_0 :
    savedBlockClass (75*232+0) = some 98 ∧
    recordedClassRoot 98 = 3810 := by decide +kernel

theorem completed_232_0 (code : Nat) :
    weight completedCredit 0 232 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 232 [] 2 16
    (fun code => 0) selected_232_0 direction_232.1
    direction_232.2.1 conditioned_232 code

theorem conditional_232_0 (code : Nat) :
    weight conditionalCredit 0 232 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 232 [] 2 16
    (fun code => 0) selected_232_0 direction_232.1
    direction_232.2.2 conditioned_232 code
#print axioms selected_232_0
#print axioms source_232_0
#print axioms target_232_0
#print axioms block_232_0
#print axioms completed_232_0
#print axioms conditional_232_0

theorem selected_232_3 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 3 [] ++ [232])) := by rfl

theorem source_232_3 (code : Nat) :
    edgeSource 3 232 code = 1041984+code/6 := by rfl

theorem target_232_3 (code : Nat) :
    edgeTarget 3 232 code = 155520+code%7776 := by rfl

theorem block_232_3 :
    savedBlockClass (75*232+3) = some 98 ∧
    recordedClassRoot 98 = 3810 := by decide +kernel

theorem completed_232_3 (code : Nat) :
    weight completedCredit 3 232 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 3 232 [] 2 16
    (fun code => 0) selected_232_3 direction_232.1
    direction_232.2.1 conditioned_232 code

theorem conditional_232_3 (code : Nat) :
    weight conditionalCredit 3 232 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 3 232 [] 2 16
    (fun code => 0) selected_232_3 direction_232.1
    direction_232.2.2 conditioned_232 code
#print axioms selected_232_3
#print axioms source_232_3
#print axioms target_232_3
#print axioms block_232_3
#print axioms completed_232_3
#print axioms conditional_232_3

theorem selected_233_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [233])) := by rfl

theorem source_233_0 (code : Nat) :
    edgeSource 0 233 code = 513216+code/6 := by rfl

theorem target_233_0 (code : Nat) :
    edgeTarget 0 233 code = 163296+code%7776 := by rfl

theorem block_233_0 :
    savedBlockClass (75*233+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_233_0 (code : Nat) :
    weight completedCredit 0 233 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 233 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_233_0 direction_233.1
    direction_233.2.1 conditioned_233 code

theorem conditional_233_0 (code : Nat) :
    weight conditionalCredit 0 233 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 233 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_233_0 direction_233.1
    direction_233.2.2 conditioned_233 code
#print axioms selected_233_0
#print axioms source_233_0
#print axioms target_233_0
#print axioms block_233_0
#print axioms completed_233_0
#print axioms conditional_233_0

theorem selected_233_3 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 3 [] ++ [233])) := by rfl

theorem source_233_3 (code : Nat) :
    edgeSource 3 233 code = 1041984+code/6 := by rfl

theorem target_233_3 (code : Nat) :
    edgeTarget 3 233 code = 163296+code%7776 := by rfl

theorem block_233_3 :
    savedBlockClass (75*233+3) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_233_3 (code : Nat) :
    weight completedCredit 3 233 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 3 233 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_233_3 direction_233.1
    direction_233.2.1 conditioned_233 code

theorem conditional_233_3 (code : Nat) :
    weight conditionalCredit 3 233 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 3 233 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_233_3 direction_233.1
    direction_233.2.2 conditioned_233 code
#print axioms selected_233_3
#print axioms source_233_3
#print axioms target_233_3
#print axioms block_233_3
#print axioms completed_233_3
#print axioms conditional_233_3

theorem selected_234_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [234])) := by rfl

theorem source_234_0 (code : Nat) :
    edgeSource 0 234 code = 513216+code/6 := by rfl

theorem target_234_0 (code : Nat) :
    edgeTarget 0 234 code = 171072+code%7776 := by rfl

theorem block_234_0 :
    savedBlockClass (75*234+0) = some 100 ∧
    recordedClassRoot 100 = 3818 := by decide +kernel

theorem completed_234_0 (code : Nat) :
    weight completedCredit 0 234 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 234 [] 2 0
    (fun code => 0) selected_234_0 direction_234.1
    direction_234.2.1 conditioned_234 code

theorem conditional_234_0 (code : Nat) :
    weight conditionalCredit 0 234 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 234 [] 2 16
    (fun code => 0) selected_234_0 direction_234.1
    direction_234.2.2 conditioned_234 code
#print axioms selected_234_0
#print axioms source_234_0
#print axioms target_234_0
#print axioms block_234_0
#print axioms completed_234_0
#print axioms conditional_234_0

theorem selected_234_3 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 3 [] ++ [234])) := by rfl

theorem source_234_3 (code : Nat) :
    edgeSource 3 234 code = 1041984+code/6 := by rfl

theorem target_234_3 (code : Nat) :
    edgeTarget 3 234 code = 171072+code%7776 := by rfl

theorem block_234_3 :
    savedBlockClass (75*234+3) = some 100 ∧
    recordedClassRoot 100 = 3818 := by decide +kernel

theorem completed_234_3 (code : Nat) :
    weight completedCredit 3 234 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 3 234 [] 2 0
    (fun code => 0) selected_234_3 direction_234.1
    direction_234.2.1 conditioned_234 code

theorem conditional_234_3 (code : Nat) :
    weight conditionalCredit 3 234 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 3 234 [] 2 16
    (fun code => 0) selected_234_3 direction_234.1
    direction_234.2.2 conditioned_234 code
#print axioms selected_234_3
#print axioms source_234_3
#print axioms target_234_3
#print axioms block_234_3
#print axioms completed_234_3
#print axioms conditional_234_3

theorem selected_235_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [235])) := by rfl

theorem source_235_0 (code : Nat) :
    edgeSource 0 235 code = 513216+code/6 := by rfl

theorem target_235_0 (code : Nat) :
    edgeTarget 0 235 code = 1135296+code%7776 := by rfl

theorem block_235_0 :
    savedBlockClass (75*235+0) = some 101 ∧
    recordedClassRoot 101 = 3823 := by decide +kernel

theorem completed_235_0 (code : Nat) :
    weight completedCredit 0 235 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 235 [] 2 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_235_0 direction_235.1
    direction_235.2.1 conditioned_235 code

theorem conditional_235_0 (code : Nat) :
    weight conditionalCredit 0 235 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 235 [] 2 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_235_0 direction_235.1
    direction_235.2.2 conditioned_235 code
#print axioms selected_235_0
#print axioms source_235_0
#print axioms target_235_0
#print axioms block_235_0
#print axioms completed_235_0
#print axioms conditional_235_0

theorem selected_235_3 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 3 [] ++ [235])) := by rfl

theorem source_235_3 (code : Nat) :
    edgeSource 3 235 code = 1041984+code/6 := by rfl

theorem target_235_3 (code : Nat) :
    edgeTarget 3 235 code = 1283040+code%7776 := by rfl

theorem block_235_3 :
    savedBlockClass (75*235+3) = some 101 ∧
    recordedClassRoot 101 = 3823 := by decide +kernel

theorem completed_235_3 (code : Nat) :
    weight completedCredit 3 235 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 3 235 [] 2 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_235_3 direction_235.1
    direction_235.2.1 conditioned_235 code

theorem conditional_235_3 (code : Nat) :
    weight conditionalCredit 3 235 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 3 235 [] 2 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_235_3 direction_235.1
    direction_235.2.2 conditioned_235 code
#print axioms selected_235_3
#print axioms source_235_3
#print axioms target_235_3
#print axioms block_235_3
#print axioms completed_235_3
#print axioms conditional_235_3

theorem selected_236_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [236])) := by rfl

theorem source_236_0 (code : Nat) :
    edgeSource 0 236 code = 513216+code/6 := by rfl

theorem target_236_0 (code : Nat) :
    edgeTarget 0 236 code = 186624+code%7776 := by rfl

theorem block_236_0 :
    savedBlockClass (75*236+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_236_0 (code : Nat) :
    weight completedCredit 0 236 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 236 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_236_0 direction_236.1
    direction_236.2.1 conditioned_236 code

theorem conditional_236_0 (code : Nat) :
    weight conditionalCredit 0 236 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 236 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_236_0 direction_236.1
    direction_236.2.2 conditioned_236 code
#print axioms selected_236_0
#print axioms source_236_0
#print axioms target_236_0
#print axioms block_236_0
#print axioms completed_236_0
#print axioms conditional_236_0

theorem selected_236_3 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 3 [] ++ [236])) := by rfl

theorem source_236_3 (code : Nat) :
    edgeSource 3 236 code = 1041984+code/6 := by rfl

theorem target_236_3 (code : Nat) :
    edgeTarget 3 236 code = 186624+code%7776 := by rfl

theorem block_236_3 :
    savedBlockClass (75*236+3) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_236_3 (code : Nat) :
    weight completedCredit 3 236 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 3 236 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_236_3 direction_236.1
    direction_236.2.1 conditioned_236 code

theorem conditional_236_3 (code : Nat) :
    weight conditionalCredit 3 236 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 3 236 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_236_3 direction_236.1
    direction_236.2.2 conditioned_236 code
#print axioms selected_236_3
#print axioms source_236_3
#print axioms target_236_3
#print axioms block_236_3
#print axioms completed_236_3
#print axioms conditional_236_3

theorem selected_237_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [237])) := by rfl

theorem source_237_0 (code : Nat) :
    edgeSource 0 237 code = 520992+code/6 := by rfl

theorem target_237_0 (code : Nat) :
    edgeTarget 0 237 code = 536544+code%7776 := by rfl

theorem block_237_0 :
    savedBlockClass (75*237+0) = some 112 ∧
    recordedClassRoot 112 = 3904 := by decide +kernel

theorem completed_237_0 (code : Nat) :
    weight completedCredit 0 237 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 237 [] 5 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_237_0 direction_237.1
    direction_237.2.1 conditioned_237 code

theorem conditional_237_0 (code : Nat) :
    weight conditionalCredit 0 237 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 237 [] 5 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_237_0 direction_237.1
    direction_237.2.2 conditioned_237 code
#print axioms selected_237_0
#print axioms source_237_0
#print axioms target_237_0
#print axioms block_237_0
#print axioms completed_237_0
#print axioms conditional_237_0

theorem selected_238_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [238])) := by rfl

theorem source_238_0 (code : Nat) :
    edgeSource 0 238 code = 520992+code/6 := by rfl

theorem target_238_0 (code : Nat) :
    edgeTarget 0 238 code = 544320+code%7776 := by rfl

theorem block_238_0 :
    savedBlockClass (75*238+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_238_0 (code : Nat) :
    weight completedCredit 0 238 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 238 [] 21 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_238_0 direction_238.1
    direction_238.2.1 conditioned_238 code

theorem conditional_238_0 (code : Nat) :
    weight conditionalCredit 0 238 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 238 [] 21 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_238_0 direction_238.1
    direction_238.2.2 conditioned_238 code
#print axioms selected_238_0
#print axioms source_238_0
#print axioms target_238_0
#print axioms block_238_0
#print axioms completed_238_0
#print axioms conditional_238_0

theorem selected_239_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [239])) := by rfl

theorem source_239_0 (code : Nat) :
    edgeSource 0 239 code = 528768+code/6 := by rfl

theorem target_239_0 (code : Nat) :
    edgeTarget 0 239 code = 567648+code%7776 := by rfl

theorem block_239_0 :
    savedBlockClass (75*239+0) = some 77 ∧
    recordedClassRoot 77 = 3522 := by decide +kernel

theorem completed_239_0 (code : Nat) :
    weight completedCredit 0 239 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 239 [] 12 16
    (fun code => 0) selected_239_0 direction_239.1
    direction_239.2.1 conditioned_239 code

theorem conditional_239_0 (code : Nat) :
    weight conditionalCredit 0 239 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 239 [] 12 16
    (fun code => 0) selected_239_0 direction_239.1
    direction_239.2.2 conditioned_239 code
#print axioms selected_239_0
#print axioms source_239_0
#print axioms target_239_0
#print axioms block_239_0
#print axioms completed_239_0
#print axioms conditional_239_0

theorem selected_240_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [240])) := by rfl

theorem source_240_0 (code : Nat) :
    edgeSource 0 240 code = 528768+code/6 := by rfl

theorem target_240_0 (code : Nat) :
    edgeTarget 0 240 code = 575424+code%7776 := by rfl

theorem block_240_0 :
    savedBlockClass (75*240+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_240_0 (code : Nat) :
    weight completedCredit 0 240 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 240 [] 22 16
    (fun code => 0) selected_240_0 direction_240.1
    direction_240.2.1 conditioned_240 code

theorem conditional_240_0 (code : Nat) :
    weight conditionalCredit 0 240 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 240 [] 22 16
    (fun code => 0) selected_240_0 direction_240.1
    direction_240.2.2 conditioned_240 code
#print axioms selected_240_0
#print axioms source_240_0
#print axioms target_240_0
#print axioms block_240_0
#print axioms completed_240_0
#print axioms conditional_240_0

theorem selected_241_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [241])) := by rfl

theorem source_241_0 (code : Nat) :
    edgeSource 0 241 code = 536544+code/6 := by rfl

theorem target_241_0 (code : Nat) :
    edgeTarget 0 241 code = 598752+code%7776 := by rfl

theorem block_241_0 :
    savedBlockClass (75*241+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_241_0 (code : Nat) :
    weight completedCredit 0 241 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 241 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_241_0 direction_241.1
    direction_241.2.1 conditioned_241 code

theorem conditional_241_0 (code : Nat) :
    weight conditionalCredit 0 241 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 241 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_241_0 direction_241.1
    direction_241.2.2 conditioned_241 code
#print axioms selected_241_0
#print axioms source_241_0
#print axioms target_241_0
#print axioms block_241_0
#print axioms completed_241_0
#print axioms conditional_241_0

theorem selected_242_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [242])) := by rfl

theorem source_242_0 (code : Nat) :
    edgeSource 0 242 code = 544320+code/6 := by rfl

theorem target_242_0 (code : Nat) :
    edgeTarget 0 242 code = 629856+code%7776 := by rfl

theorem block_242_0 :
    savedBlockClass (75*242+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_242_0 (code : Nat) :
    weight completedCredit 0 242 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 242 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_242_0 direction_242.1
    direction_242.2.1 conditioned_242 code

theorem conditional_242_0 (code : Nat) :
    weight conditionalCredit 0 242 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 242 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_242_0 direction_242.1
    direction_242.2.2 conditioned_242 code
#print axioms selected_242_0
#print axioms source_242_0
#print axioms target_242_0
#print axioms block_242_0
#print axioms completed_242_0
#print axioms conditional_242_0

theorem selected_243_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [243])) := by rfl

theorem source_243_0 (code : Nat) :
    edgeSource 0 243 code = 544320+code/6 := by rfl

theorem target_243_0 (code : Nat) :
    edgeTarget 0 243 code = 606528+code%7776 := by rfl

theorem block_243_0 :
    savedBlockClass (75*243+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_243_0 (code : Nat) :
    weight completedCredit 0 243 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 243 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_243_0 direction_243.1
    direction_243.2.1 conditioned_243 code

theorem conditional_243_0 (code : Nat) :
    weight conditionalCredit 0 243 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 243 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_243_0 direction_243.1
    direction_243.2.2 conditioned_243 code
#print axioms selected_243_0
#print axioms source_243_0
#print axioms target_243_0
#print axioms block_243_0
#print axioms completed_243_0
#print axioms conditional_243_0

theorem selected_244_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [244])) := by rfl

theorem source_244_0 (code : Nat) :
    edgeSource 0 244 code = 544320+code/6 := by rfl

theorem target_244_0 (code : Nat) :
    edgeTarget 0 244 code = 614304+code%7776 := by rfl

theorem block_244_0 :
    savedBlockClass (75*244+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_244_0 (code : Nat) :
    weight completedCredit 0 244 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 244 [] 0 0
    (fun code => 0) selected_244_0 direction_244.1
    direction_244.2.1 conditioned_244 code

theorem conditional_244_0 (code : Nat) :
    weight conditionalCredit 0 244 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 244 [] 0 16
    (fun code => 0) selected_244_0 direction_244.1
    direction_244.2.2 conditioned_244 code
#print axioms selected_244_0
#print axioms source_244_0
#print axioms target_244_0
#print axioms block_244_0
#print axioms completed_244_0
#print axioms conditional_244_0

theorem selected_245_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [245])) := by rfl

theorem source_245_0 (code : Nat) :
    edgeSource 0 245 code = 544320+code/6 := by rfl

theorem target_245_0 (code : Nat) :
    edgeTarget 0 245 code = 622080+code%7776 := by rfl

theorem block_245_0 :
    savedBlockClass (75*245+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_245_0 (code : Nat) :
    weight completedCredit 0 245 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 245 [] 0 16
    (fun code => 0) selected_245_0 direction_245.1
    direction_245.2.1 conditioned_245 code

theorem conditional_245_0 (code : Nat) :
    weight conditionalCredit 0 245 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 245 [] 0 16
    (fun code => 0) selected_245_0 direction_245.1
    direction_245.2.2 conditioned_245 code
#print axioms selected_245_0
#print axioms source_245_0
#print axioms target_245_0
#print axioms block_245_0
#print axioms completed_245_0
#print axioms conditional_245_0

theorem selected_246_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [246])) := by rfl

theorem source_246_0 (code : Nat) :
    edgeSource 0 246 code = 544320+code/6 := by rfl

theorem target_246_0 (code : Nat) :
    edgeTarget 0 246 code = 637632+code%7776 := by rfl

theorem block_246_0 :
    savedBlockClass (75*246+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_246_0 (code : Nat) :
    weight completedCredit 0 246 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 246 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_246_0 direction_246.1
    direction_246.2.1 conditioned_246 code

theorem conditional_246_0 (code : Nat) :
    weight conditionalCredit 0 246 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 246 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_246_0 direction_246.1
    direction_246.2.2 conditioned_246 code
#print axioms selected_246_0
#print axioms source_246_0
#print axioms target_246_0
#print axioms block_246_0
#print axioms completed_246_0
#print axioms conditional_246_0

theorem selected_247_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [247])) := by rfl

theorem source_247_0 (code : Nat) :
    edgeSource 0 247 code = 552096+code/6 := by rfl

theorem target_247_0 (code : Nat) :
    edgeTarget 0 247 code = 660960+code%7776 := by rfl

theorem block_247_0 :
    savedBlockClass (75*247+0) = some 115 ∧
    recordedClassRoot 115 = 3910 := by decide +kernel

theorem completed_247_0 (code : Nat) :
    weight completedCredit 0 247 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 247 [] 22 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_247_0 direction_247.1
    direction_247.2.1 conditioned_247 code

theorem conditional_247_0 (code : Nat) :
    weight conditionalCredit 0 247 code =
      120*(code%6+1)+max (max 22 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 247 [] 22 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_247_0 direction_247.1
    direction_247.2.2 conditioned_247 code
#print axioms selected_247_0
#print axioms source_247_0
#print axioms target_247_0
#print axioms block_247_0
#print axioms completed_247_0
#print axioms conditional_247_0

theorem selected_248_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [248])) := by rfl

theorem source_248_0 (code : Nat) :
    edgeSource 0 248 code = 552096+code/6 := by rfl

theorem target_248_0 (code : Nat) :
    edgeTarget 0 248 code = 668736+code%7776 := by rfl

theorem block_248_0 :
    savedBlockClass (75*248+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_248_0 (code : Nat) :
    weight completedCredit 0 248 code =
      120*(code%6+1)+max (max 43 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 248 [] 43 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_248_0 direction_248.1
    direction_248.2.1 conditioned_248 code

theorem conditional_248_0 (code : Nat) :
    weight conditionalCredit 0 248 code =
      120*(code%6+1)+max (max 43 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 248 [] 43 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_248_0 direction_248.1
    direction_248.2.2 conditioned_248 code
#print axioms selected_248_0
#print axioms source_248_0
#print axioms target_248_0
#print axioms block_248_0
#print axioms completed_248_0
#print axioms conditional_248_0

theorem selected_249_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [249])) := by rfl

theorem source_249_0 (code : Nat) :
    edgeSource 0 249 code = 559872+code/6 := by rfl

theorem target_249_0 (code : Nat) :
    edgeTarget 0 249 code = 684288+code%7776 := by rfl

theorem block_249_0 :
    savedBlockClass (75*249+0) = some 116 ∧
    recordedClassRoot 116 = 3930 := by decide +kernel

theorem completed_249_0 (code : Nat) :
    weight completedCredit 0 249 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 249 [] 5 16
    (fun code => 0) selected_249_0 direction_249.1
    direction_249.2.1 conditioned_249 code

theorem conditional_249_0 (code : Nat) :
    weight conditionalCredit 0 249 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 249 [] 5 16
    (fun code => 0) selected_249_0 direction_249.1
    direction_249.2.2 conditioned_249 code
#print axioms selected_249_0
#print axioms source_249_0
#print axioms target_249_0
#print axioms block_249_0
#print axioms completed_249_0
#print axioms conditional_249_0

theorem selected_250_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [250])) := by rfl

theorem source_250_0 (code : Nat) :
    edgeSource 0 250 code = 567648+code/6 := by rfl

theorem target_250_0 (code : Nat) :
    edgeTarget 0 250 code = 699840+code%7776 := by rfl

theorem block_250_0 :
    savedBlockClass (75*250+0) = some 117 ∧
    recordedClassRoot 117 = 3932 := by decide +kernel

theorem completed_250_0 (code : Nat) :
    weight completedCredit 0 250 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 250 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_250_0 direction_250.1
    direction_250.2.1 conditioned_250 code

theorem conditional_250_0 (code : Nat) :
    weight conditionalCredit 0 250 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 250 [] 10 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_250_0 direction_250.1
    direction_250.2.2 conditioned_250 code
#print axioms selected_250_0
#print axioms source_250_0
#print axioms target_250_0
#print axioms block_250_0
#print axioms completed_250_0
#print axioms conditional_250_0

theorem selected_251_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [251])) := by rfl

theorem source_251_0 (code : Nat) :
    edgeSource 0 251 code = 575424+code/6 := by rfl

theorem target_251_0 (code : Nat) :
    edgeTarget 0 251 code = 730944+code%7776 := by rfl

theorem block_251_0 :
    savedBlockClass (75*251+0) = some 115 ∧
    recordedClassRoot 115 = 3910 := by decide +kernel

theorem completed_251_0 (code : Nat) :
    weight completedCredit 0 251 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 251 [] 13 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_251_0 direction_251.1
    direction_251.2.1 conditioned_251 code

theorem conditional_251_0 (code : Nat) :
    weight conditionalCredit 0 251 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 251 [] 13 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_251_0 direction_251.1
    direction_251.2.2 conditioned_251 code
#print axioms selected_251_0
#print axioms source_251_0
#print axioms target_251_0
#print axioms block_251_0
#print axioms completed_251_0
#print axioms conditional_251_0

theorem selected_252_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [252])) := by rfl

theorem source_252_0 (code : Nat) :
    edgeSource 0 252 code = 575424+code/6 := by rfl

theorem target_252_0 (code : Nat) :
    edgeTarget 0 252 code = 707616+code%7776 := by rfl

theorem block_252_0 :
    savedBlockClass (75*252+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_252_0 (code : Nat) :
    weight completedCredit 0 252 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 252 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_252_0 direction_252.1
    direction_252.2.1 conditioned_252 code

theorem conditional_252_0 (code : Nat) :
    weight conditionalCredit 0 252 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 252 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_252_0 direction_252.1
    direction_252.2.2 conditioned_252 code
#print axioms selected_252_0
#print axioms source_252_0
#print axioms target_252_0
#print axioms block_252_0
#print axioms completed_252_0
#print axioms conditional_252_0

theorem selected_253_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [253])) := by rfl

theorem source_253_0 (code : Nat) :
    edgeSource 0 253 code = 575424+code/6 := by rfl

theorem target_253_0 (code : Nat) :
    edgeTarget 0 253 code = 715392+code%7776 := by rfl

theorem block_253_0 :
    savedBlockClass (75*253+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_253_0 (code : Nat) :
    weight completedCredit 0 253 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 253 [] 13 0
    (fun code => 0) selected_253_0 direction_253.1
    direction_253.2.1 conditioned_253 code

theorem conditional_253_0 (code : Nat) :
    weight conditionalCredit 0 253 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 253 [] 13 16
    (fun code => 0) selected_253_0 direction_253.1
    direction_253.2.2 conditioned_253 code
#print axioms selected_253_0
#print axioms source_253_0
#print axioms target_253_0
#print axioms block_253_0
#print axioms completed_253_0
#print axioms conditional_253_0

theorem selected_254_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [254])) := by rfl

theorem source_254_0 (code : Nat) :
    edgeSource 0 254 code = 575424+code/6 := by rfl

theorem target_254_0 (code : Nat) :
    edgeTarget 0 254 code = 723168+code%7776 := by rfl

theorem block_254_0 :
    savedBlockClass (75*254+0) = some 40 ∧
    recordedClassRoot 40 = 3139 := by decide +kernel

theorem completed_254_0 (code : Nat) :
    weight completedCredit 0 254 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 254 [] 13 16
    (fun code => 0) selected_254_0 direction_254.1
    direction_254.2.1 conditioned_254 code

theorem conditional_254_0 (code : Nat) :
    weight conditionalCredit 0 254 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 254 [] 13 16
    (fun code => 0) selected_254_0 direction_254.1
    direction_254.2.2 conditioned_254 code
#print axioms selected_254_0
#print axioms source_254_0
#print axioms target_254_0
#print axioms block_254_0
#print axioms completed_254_0
#print axioms conditional_254_0

theorem selected_255_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [255])) := by rfl

theorem source_255_0 (code : Nat) :
    edgeSource 0 255 code = 575424+code/6 := by rfl

theorem target_255_0 (code : Nat) :
    edgeTarget 0 255 code = 738720+code%7776 := by rfl

theorem block_255_0 :
    savedBlockClass (75*255+0) = some 38 ∧
    recordedClassRoot 38 = 2979 := by decide +kernel

theorem completed_255_0 (code : Nat) :
    weight completedCredit 0 255 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 255 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_255_0 direction_255.1
    direction_255.2.1 conditioned_255 code

theorem conditional_255_0 (code : Nat) :
    weight conditionalCredit 0 255 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 255 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_255_0 direction_255.1
    direction_255.2.2 conditioned_255 code
#print axioms selected_255_0
#print axioms source_255_0
#print axioms target_255_0
#print axioms block_255_0
#print axioms completed_255_0
#print axioms conditional_255_0

theorem selected_256_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [256])) := by rfl

theorem source_256_0 (code : Nat) :
    edgeSource 0 256 code = 583200+code/6 := by rfl

theorem target_256_0 (code : Nat) :
    edgeTarget 0 256 code = 762048+code%7776 := by rfl

theorem block_256_0 :
    savedBlockClass (75*256+0) = some 118 ∧
    recordedClassRoot 118 = 3934 := by decide +kernel

theorem completed_256_0 (code : Nat) :
    weight completedCredit 0 256 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 256 [] 8 0
    (fun code => 0) selected_256_0 direction_256.1
    direction_256.2.1 conditioned_256 code

theorem conditional_256_0 (code : Nat) :
    weight conditionalCredit 0 256 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 256 [] 8 16
    (fun code => 0) selected_256_0 direction_256.1
    direction_256.2.2 conditioned_256 code
#print axioms selected_256_0
#print axioms source_256_0
#print axioms target_256_0
#print axioms block_256_0
#print axioms completed_256_0
#print axioms conditional_256_0

theorem selected_257_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [257])) := by rfl

theorem source_257_0 (code : Nat) :
    edgeSource 0 257 code = 583200+code/6 := by rfl

theorem target_257_0 (code : Nat) :
    edgeTarget 0 257 code = 769824+code%7776 := by rfl

theorem block_257_0 :
    savedBlockClass (75*257+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_257_0 (code : Nat) :
    weight completedCredit 0 257 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 257 [] 18 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_257_0 direction_257.1
    direction_257.2.1 conditioned_257 code

theorem conditional_257_0 (code : Nat) :
    weight conditionalCredit 0 257 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 257 [] 18 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_257_0 direction_257.1
    direction_257.2.2 conditioned_257 code
#print axioms selected_257_0
#print axioms source_257_0
#print axioms target_257_0
#print axioms block_257_0
#print axioms completed_257_0
#print axioms conditional_257_0

theorem selected_258_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [258])) := by rfl

theorem source_258_0 (code : Nat) :
    edgeSource 0 258 code = 590976+code/6 := by rfl

theorem target_258_0 (code : Nat) :
    edgeTarget 0 258 code = 1143072+code%7776 := by rfl

theorem block_258_0 :
    savedBlockClass (75*258+0) = some 120 ∧
    recordedClassRoot 120 = 3938 := by decide +kernel

theorem completed_258_0 (code : Nat) :
    weight completedCredit 0 258 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 258 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_258_0 direction_258.1
    direction_258.2.1 conditioned_258 code

theorem conditional_258_0 (code : Nat) :
    weight conditionalCredit 0 258 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 258 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_258_0 direction_258.1
    direction_258.2.2 conditioned_258 code
#print axioms selected_258_0
#print axioms source_258_0
#print axioms target_258_0
#print axioms block_258_0
#print axioms completed_258_0
#print axioms conditional_258_0

theorem selected_259_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [259])) := by rfl

theorem source_259_0 (code : Nat) :
    edgeSource 0 259 code = 598752+code/6 := by rfl

theorem target_259_0 (code : Nat) :
    edgeTarget 0 259 code = 816480+code%7776 := by rfl

theorem block_259_0 :
    savedBlockClass (75*259+0) = some 118 ∧
    recordedClassRoot 118 = 3934 := by decide +kernel

theorem completed_259_0 (code : Nat) :
    weight completedCredit 0 259 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 259 [] 5 0
    (fun code => 0) selected_259_0 direction_259.1
    direction_259.2.1 conditioned_259 code

theorem conditional_259_0 (code : Nat) :
    weight conditionalCredit 0 259 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 259 [] 5 16
    (fun code => 0) selected_259_0 direction_259.1
    direction_259.2.2 conditioned_259 code
#print axioms selected_259_0
#print axioms source_259_0
#print axioms target_259_0
#print axioms block_259_0
#print axioms completed_259_0
#print axioms conditional_259_0

theorem selected_260_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [260])) := by rfl

theorem source_260_0 (code : Nat) :
    edgeSource 0 260 code = 598752+code/6 := by rfl

theorem target_260_0 (code : Nat) :
    edgeTarget 0 260 code = 793152+code%7776 := by rfl

theorem block_260_0 :
    savedBlockClass (75*260+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_260_0 (code : Nat) :
    weight completedCredit 0 260 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 260 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_260_0 direction_260.1
    direction_260.2.1 conditioned_260 code

theorem conditional_260_0 (code : Nat) :
    weight conditionalCredit 0 260 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 260 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_260_0 direction_260.1
    direction_260.2.2 conditioned_260 code
#print axioms selected_260_0
#print axioms source_260_0
#print axioms target_260_0
#print axioms block_260_0
#print axioms completed_260_0
#print axioms conditional_260_0

theorem selected_261_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [261])) := by rfl

theorem source_261_0 (code : Nat) :
    edgeSource 0 261 code = 598752+code/6 := by rfl

theorem target_261_0 (code : Nat) :
    edgeTarget 0 261 code = 800928+code%7776 := by rfl

theorem block_261_0 :
    savedBlockClass (75*261+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_261_0 (code : Nat) :
    weight completedCredit 0 261 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 261 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_261_0 direction_261.1
    direction_261.2.1 conditioned_261 code

theorem conditional_261_0 (code : Nat) :
    weight conditionalCredit 0 261 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 261 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_261_0 direction_261.1
    direction_261.2.2 conditioned_261 code
#print axioms selected_261_0
#print axioms source_261_0
#print axioms target_261_0
#print axioms block_261_0
#print axioms completed_261_0
#print axioms conditional_261_0

theorem selected_262_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [262])) := by rfl

theorem source_262_0 (code : Nat) :
    edgeSource 0 262 code = 598752+code/6 := by rfl

theorem target_262_0 (code : Nat) :
    edgeTarget 0 262 code = 808704+code%7776 := by rfl

theorem block_262_0 :
    savedBlockClass (75*262+0) = some 121 ∧
    recordedClassRoot 121 = 3940 := by decide +kernel

theorem completed_262_0 (code : Nat) :
    weight completedCredit 0 262 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 262 [] 10 16
    (fun code => 0) selected_262_0 direction_262.1
    direction_262.2.1 conditioned_262 code

theorem conditional_262_0 (code : Nat) :
    weight conditionalCredit 0 262 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 262 [] 10 16
    (fun code => 0) selected_262_0 direction_262.1
    direction_262.2.2 conditioned_262 code
#print axioms selected_262_0
#print axioms source_262_0
#print axioms target_262_0
#print axioms block_262_0
#print axioms completed_262_0
#print axioms conditional_262_0

theorem selected_263_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [263])) := by rfl

theorem source_263_0 (code : Nat) :
    edgeSource 0 263 code = 598752+code/6 := by rfl

theorem target_263_0 (code : Nat) :
    edgeTarget 0 263 code = 824256+code%7776 := by rfl

theorem block_263_0 :
    savedBlockClass (75*263+0) = some 119 ∧
    recordedClassRoot 119 = 3936 := by decide +kernel

theorem completed_263_0 (code : Nat) :
    weight completedCredit 0 263 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 263 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_263_0 direction_263.1
    direction_263.2.1 conditioned_263 code

theorem conditional_263_0 (code : Nat) :
    weight conditionalCredit 0 263 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 263 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_263_0 direction_263.1
    direction_263.2.2 conditioned_263 code
#print axioms selected_263_0
#print axioms source_263_0
#print axioms target_263_0
#print axioms block_263_0
#print axioms completed_263_0
#print axioms conditional_263_0

theorem selected_264_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [264])) := by rfl

theorem source_264_0 (code : Nat) :
    edgeSource 0 264 code = 606528+code/6 := by rfl

theorem target_264_0 (code : Nat) :
    edgeTarget 0 264 code = 1150848+code%7776 := by rfl

theorem block_264_0 :
    savedBlockClass (75*264+0) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_264_0 (code : Nat) :
    weight completedCredit 0 264 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 264 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_264_0 direction_264.1
    direction_264.2.1 conditioned_264 code

theorem conditional_264_0 (code : Nat) :
    weight conditionalCredit 0 264 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 264 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_264_0 direction_264.1
    direction_264.2.2 conditioned_264 code
#print axioms selected_264_0
#print axioms source_264_0
#print axioms target_264_0
#print axioms block_264_0
#print axioms completed_264_0
#print axioms conditional_264_0

theorem selected_264_45 :
    [rule024] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 45 [] ++ [264])) := by rfl

theorem source_264_45 (code : Nat) :
    edgeSource 45 264 code = 1368576+code/6 := by rfl

theorem target_264_45 (code : Nat) :
    edgeTarget 45 264 code = 1150848+code%7776 := by rfl

theorem block_264_45 :
    savedBlockClass (75*264+45) = some 114 ∧
    recordedClassRoot 114 = 3908 := by decide +kernel

theorem completed_264_45 (code : Nat) :
    weight completedCredit 45 264 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule024] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 45 264 [rule024] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_264_45 direction_264.1
    direction_264.2.1 conditioned_264 code

theorem conditional_264_45 (code : Nat) :
    weight conditionalCredit 45 264 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule024] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 45 264 [rule024] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_264_45 direction_264.1
    direction_264.2.2 conditioned_264 code
#print axioms selected_264_45
#print axioms source_264_45
#print axioms target_264_45
#print axioms block_264_45
#print axioms completed_264_45
#print axioms conditional_264_45

theorem selected_265_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [265])) := by rfl

theorem source_265_0 (code : Nat) :
    edgeSource 0 265 code = 606528+code/6 := by rfl

theorem target_265_0 (code : Nat) :
    edgeTarget 0 265 code = 832032+code%7776 := by rfl

theorem block_265_0 :
    savedBlockClass (75*265+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_265_0 (code : Nat) :
    weight completedCredit 0 265 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 265 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_265_0 direction_265.1
    direction_265.2.1 conditioned_265 code

theorem conditional_265_0 (code : Nat) :
    weight conditionalCredit 0 265 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 265 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_265_0 direction_265.1
    direction_265.2.2 conditioned_265 code
#print axioms selected_265_0
#print axioms source_265_0
#print axioms target_265_0
#print axioms block_265_0
#print axioms completed_265_0
#print axioms conditional_265_0

theorem selected_265_45 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 45 [] ++ [265])) := by rfl

theorem source_265_45 (code : Nat) :
    edgeSource 45 265 code = 1368576+code/6 := by rfl

theorem target_265_45 (code : Nat) :
    edgeTarget 45 265 code = 832032+code%7776 := by rfl

theorem block_265_45 :
    savedBlockClass (75*265+45) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_265_45 (code : Nat) :
    weight completedCredit 45 265 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 45 265 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_265_45 direction_265.1
    direction_265.2.1 conditioned_265 code

theorem conditional_265_45 (code : Nat) :
    weight conditionalCredit 45 265 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 45 265 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_265_45 direction_265.1
    direction_265.2.2 conditioned_265 code
#print axioms selected_265_45
#print axioms source_265_45
#print axioms target_265_45
#print axioms block_265_45
#print axioms completed_265_45
#print axioms conditional_265_45

theorem selected_266_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [266])) := by rfl

theorem source_266_0 (code : Nat) :
    edgeSource 0 266 code = 606528+code/6 := by rfl

theorem target_266_0 (code : Nat) :
    edgeTarget 0 266 code = 839808+code%7776 := by rfl

theorem block_266_0 :
    savedBlockClass (75*266+0) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_266_0 (code : Nat) :
    weight completedCredit 0 266 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 266 [] 0 0
    (fun code => 0) selected_266_0 direction_266.1
    direction_266.2.1 conditioned_266 code

theorem conditional_266_0 (code : Nat) :
    weight conditionalCredit 0 266 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 266 [] 0 16
    (fun code => 0) selected_266_0 direction_266.1
    direction_266.2.2 conditioned_266 code
#print axioms selected_266_0
#print axioms source_266_0
#print axioms target_266_0
#print axioms block_266_0
#print axioms completed_266_0
#print axioms conditional_266_0

theorem selected_266_45 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 45 [] ++ [266])) := by rfl

theorem source_266_45 (code : Nat) :
    edgeSource 45 266 code = 1368576+code/6 := by rfl

theorem target_266_45 (code : Nat) :
    edgeTarget 45 266 code = 839808+code%7776 := by rfl

theorem block_266_45 :
    savedBlockClass (75*266+45) = some 33 ∧
    recordedClassRoot 33 = 2711 := by decide +kernel

theorem completed_266_45 (code : Nat) :
    weight completedCredit 45 266 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 45 266 [] 0 0
    (fun code => 0) selected_266_45 direction_266.1
    direction_266.2.1 conditioned_266 code

theorem conditional_266_45 (code : Nat) :
    weight conditionalCredit 45 266 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 45 266 [] 0 16
    (fun code => 0) selected_266_45 direction_266.1
    direction_266.2.2 conditioned_266 code
#print axioms selected_266_45
#print axioms source_266_45
#print axioms target_266_45
#print axioms block_266_45
#print axioms completed_266_45
#print axioms conditional_266_45

theorem selected_267_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [267])) := by rfl

theorem source_267_0 (code : Nat) :
    edgeSource 0 267 code = 606528+code/6 := by rfl

theorem target_267_0 (code : Nat) :
    edgeTarget 0 267 code = 847584+code%7776 := by rfl

theorem block_267_0 :
    savedBlockClass (75*267+0) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_267_0 (code : Nat) :
    weight completedCredit 0 267 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 267 [] 0 16
    (fun code => 0) selected_267_0 direction_267.1
    direction_267.2.1 conditioned_267 code

theorem conditional_267_0 (code : Nat) :
    weight conditionalCredit 0 267 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 267 [] 0 16
    (fun code => 0) selected_267_0 direction_267.1
    direction_267.2.2 conditioned_267 code
#print axioms selected_267_0
#print axioms source_267_0
#print axioms target_267_0
#print axioms block_267_0
#print axioms completed_267_0
#print axioms conditional_267_0

theorem selected_267_45 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 45 [] ++ [267])) := by rfl

theorem source_267_45 (code : Nat) :
    edgeSource 45 267 code = 1368576+code/6 := by rfl

theorem target_267_45 (code : Nat) :
    edgeTarget 45 267 code = 847584+code%7776 := by rfl

theorem block_267_45 :
    savedBlockClass (75*267+45) = some 14 ∧
    recordedClassRoot 14 = 2004 := by decide +kernel

theorem completed_267_45 (code : Nat) :
    weight completedCredit 45 267 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 45 267 [] 0 16
    (fun code => 0) selected_267_45 direction_267.1
    direction_267.2.1 conditioned_267 code

theorem conditional_267_45 (code : Nat) :
    weight conditionalCredit 45 267 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 45 267 [] 0 16
    (fun code => 0) selected_267_45 direction_267.1
    direction_267.2.2 conditioned_267 code
#print axioms selected_267_45
#print axioms source_267_45
#print axioms target_267_45
#print axioms block_267_45
#print axioms completed_267_45
#print axioms conditional_267_45

theorem selected_268_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [268])) := by rfl

theorem source_268_0 (code : Nat) :
    edgeSource 0 268 code = 606528+code/6 := by rfl

theorem target_268_0 (code : Nat) :
    edgeTarget 0 268 code = 863136+code%7776 := by rfl

theorem block_268_0 :
    savedBlockClass (75*268+0) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_268_0 (code : Nat) :
    weight completedCredit 0 268 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 268 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_268_0 direction_268.1
    direction_268.2.1 conditioned_268 code

theorem conditional_268_0 (code : Nat) :
    weight conditionalCredit 0 268 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 268 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_268_0 direction_268.1
    direction_268.2.2 conditioned_268 code
#print axioms selected_268_0
#print axioms source_268_0
#print axioms target_268_0
#print axioms block_268_0
#print axioms completed_268_0
#print axioms conditional_268_0

theorem selected_268_45 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 45 [] ++ [268])) := by rfl

theorem source_268_45 (code : Nat) :
    edgeSource 45 268 code = 1368576+code/6 := by rfl

theorem target_268_45 (code : Nat) :
    edgeTarget 45 268 code = 863136+code%7776 := by rfl

theorem block_268_45 :
    savedBlockClass (75*268+45) = some 34 ∧
    recordedClassRoot 34 = 2715 := by decide +kernel

theorem completed_268_45 (code : Nat) :
    weight completedCredit 45 268 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 45 268 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_268_45 direction_268.1
    direction_268.2.1 conditioned_268 code

theorem conditional_268_45 (code : Nat) :
    weight conditionalCredit 45 268 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 45 268 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_268_45 direction_268.1
    direction_268.2.2 conditioned_268 code
#print axioms selected_268_45
#print axioms source_268_45
#print axioms target_268_45
#print axioms block_268_45
#print axioms completed_268_45
#print axioms conditional_268_45

theorem selected_269_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [269])) := by rfl

theorem source_269_0 (code : Nat) :
    edgeSource 0 269 code = 614304+code/6 := by rfl

theorem target_269_0 (code : Nat) :
    edgeTarget 0 269 code = 894240+code%7776 := by rfl

theorem block_269_0 :
    savedBlockClass (75*269+0) = some 112 ∧
    recordedClassRoot 112 = 3904 := by decide +kernel

theorem completed_269_0 (code : Nat) :
    weight completedCredit 0 269 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 269 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_269_0 direction_269.1
    direction_269.2.1 conditioned_269 code

theorem conditional_269_0 (code : Nat) :
    weight conditionalCredit 0 269 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 269 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_269_0 direction_269.1
    direction_269.2.2 conditioned_269 code
#print axioms selected_269_0
#print axioms source_269_0
#print axioms target_269_0
#print axioms block_269_0
#print axioms completed_269_0
#print axioms conditional_269_0

theorem selected_270_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [270])) := by rfl

theorem source_270_0 (code : Nat) :
    edgeSource 0 270 code = 614304+code/6 := by rfl

theorem target_270_0 (code : Nat) :
    edgeTarget 0 270 code = 870912+code%7776 := by rfl

theorem block_270_0 :
    savedBlockClass (75*270+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_270_0 (code : Nat) :
    weight completedCredit 0 270 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 270 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_270_0 direction_270.1
    direction_270.2.1 conditioned_270 code

theorem conditional_270_0 (code : Nat) :
    weight conditionalCredit 0 270 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 270 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_270_0 direction_270.1
    direction_270.2.2 conditioned_270 code
#print axioms selected_270_0
#print axioms source_270_0
#print axioms target_270_0
#print axioms block_270_0
#print axioms completed_270_0
#print axioms conditional_270_0

theorem selected_271_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [271])) := by rfl

theorem source_271_0 (code : Nat) :
    edgeSource 0 271 code = 614304+code/6 := by rfl

theorem target_271_0 (code : Nat) :
    edgeTarget 0 271 code = 878688+code%7776 := by rfl

theorem block_271_0 :
    savedBlockClass (75*271+0) = some 29 ∧
    recordedClassRoot 29 = 2691 := by decide +kernel

theorem completed_271_0 (code : Nat) :
    weight completedCredit 0 271 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 271 [] 0 0
    (fun code => 0) selected_271_0 direction_271.1
    direction_271.2.1 conditioned_271 code

theorem conditional_271_0 (code : Nat) :
    weight conditionalCredit 0 271 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 271 [] 0 16
    (fun code => 0) selected_271_0 direction_271.1
    direction_271.2.2 conditioned_271 code
#print axioms selected_271_0
#print axioms source_271_0
#print axioms target_271_0
#print axioms block_271_0
#print axioms completed_271_0
#print axioms conditional_271_0

theorem selected_272_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [272])) := by rfl

theorem source_272_0 (code : Nat) :
    edgeSource 0 272 code = 614304+code/6 := by rfl

theorem target_272_0 (code : Nat) :
    edgeTarget 0 272 code = 886464+code%7776 := by rfl

theorem block_272_0 :
    savedBlockClass (75*272+0) = some 43 ∧
    recordedClassRoot 43 = 3318 := by decide +kernel

theorem completed_272_0 (code : Nat) :
    weight completedCredit 0 272 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 272 [] 0 16
    (fun code => 0) selected_272_0 direction_272.1
    direction_272.2.1 conditioned_272 code

theorem conditional_272_0 (code : Nat) :
    weight conditionalCredit 0 272 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 272 [] 0 16
    (fun code => 0) selected_272_0 direction_272.1
    direction_272.2.2 conditioned_272 code
#print axioms selected_272_0
#print axioms source_272_0
#print axioms target_272_0
#print axioms block_272_0
#print axioms completed_272_0
#print axioms conditional_272_0

theorem selected_273_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [273])) := by rfl

theorem source_273_0 (code : Nat) :
    edgeSource 0 273 code = 614304+code/6 := by rfl

theorem target_273_0 (code : Nat) :
    edgeTarget 0 273 code = 902016+code%7776 := by rfl

theorem block_273_0 :
    savedBlockClass (75*273+0) = some 30 ∧
    recordedClassRoot 30 = 2698 := by decide +kernel

theorem completed_273_0 (code : Nat) :
    weight completedCredit 0 273 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 273 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_273_0 direction_273.1
    direction_273.2.1 conditioned_273 code

theorem conditional_273_0 (code : Nat) :
    weight conditionalCredit 0 273 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 273 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_273_0 direction_273.1
    direction_273.2.2 conditioned_273 code
#print axioms selected_273_0
#print axioms source_273_0
#print axioms target_273_0
#print axioms block_273_0
#print axioms completed_273_0
#print axioms conditional_273_0

theorem selected_274_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [274])) := by rfl

theorem source_274_0 (code : Nat) :
    edgeSource 0 274 code = 622080+code/6 := by rfl

theorem target_274_0 (code : Nat) :
    edgeTarget 0 274 code = 933120+code%7776 := by rfl

theorem block_274_0 :
    savedBlockClass (75*274+0) = some 77 ∧
    recordedClassRoot 77 = 3522 := by decide +kernel

theorem completed_274_0 (code : Nat) :
    weight completedCredit 0 274 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 274 [] 12 16
    (fun code => 0) selected_274_0 direction_274.1
    direction_274.2.1 conditioned_274 code

theorem conditional_274_0 (code : Nat) :
    weight conditionalCredit 0 274 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 274 [] 12 16
    (fun code => 0) selected_274_0 direction_274.1
    direction_274.2.2 conditioned_274 code
#print axioms selected_274_0
#print axioms source_274_0
#print axioms target_274_0
#print axioms block_274_0
#print axioms completed_274_0
#print axioms conditional_274_0

theorem selected_275_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [275])) := by rfl

theorem source_275_0 (code : Nat) :
    edgeSource 0 275 code = 622080+code/6 := by rfl

theorem target_275_0 (code : Nat) :
    edgeTarget 0 275 code = 909792+code%7776 := by rfl

theorem block_275_0 :
    savedBlockClass (75*275+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_275_0 (code : Nat) :
    weight completedCredit 0 275 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 275 [] 18 16
    (fun code => 0) selected_275_0 direction_275.1
    direction_275.2.1 conditioned_275 code

theorem conditional_275_0 (code : Nat) :
    weight conditionalCredit 0 275 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 275 [] 18 16
    (fun code => 0) selected_275_0 direction_275.1
    direction_275.2.2 conditioned_275 code
#print axioms selected_275_0
#print axioms source_275_0
#print axioms target_275_0
#print axioms block_275_0
#print axioms completed_275_0
#print axioms conditional_275_0

theorem selected_276_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [276])) := by rfl

theorem source_276_0 (code : Nat) :
    edgeSource 0 276 code = 622080+code/6 := by rfl

theorem target_276_0 (code : Nat) :
    edgeTarget 0 276 code = 917568+code%7776 := by rfl

theorem block_276_0 :
    savedBlockClass (75*276+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_276_0 (code : Nat) :
    weight completedCredit 0 276 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 276 [] 18 16
    (fun code => 0) selected_276_0 direction_276.1
    direction_276.2.1 conditioned_276 code

theorem conditional_276_0 (code : Nat) :
    weight conditionalCredit 0 276 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 276 [] 18 16
    (fun code => 0) selected_276_0 direction_276.1
    direction_276.2.2 conditioned_276 code
#print axioms selected_276_0
#print axioms source_276_0
#print axioms target_276_0
#print axioms block_276_0
#print axioms completed_276_0
#print axioms conditional_276_0

theorem selected_277_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [277])) := by rfl

theorem source_277_0 (code : Nat) :
    edgeSource 0 277 code = 622080+code/6 := by rfl

theorem target_277_0 (code : Nat) :
    edgeTarget 0 277 code = 925344+code%7776 := by rfl

theorem block_277_0 :
    savedBlockClass (75*277+0) = some 76 ∧
    recordedClassRoot 76 = 3519 := by decide +kernel

theorem completed_277_0 (code : Nat) :
    weight completedCredit 0 277 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 277 [] 6 0
    (fun code => 0) selected_277_0 direction_277.1
    direction_277.2.1 conditioned_277 code

theorem conditional_277_0 (code : Nat) :
    weight conditionalCredit 0 277 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 277 [] 6 16
    (fun code => 0) selected_277_0 direction_277.1
    direction_277.2.2 conditioned_277 code
#print axioms selected_277_0
#print axioms source_277_0
#print axioms target_277_0
#print axioms block_277_0
#print axioms completed_277_0
#print axioms conditional_277_0

theorem selected_278_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [278])) := by rfl

theorem source_278_0 (code : Nat) :
    edgeSource 0 278 code = 622080+code/6 := by rfl

theorem target_278_0 (code : Nat) :
    edgeTarget 0 278 code = 940896+code%7776 := by rfl

theorem block_278_0 :
    savedBlockClass (75*278+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_278_0 (code : Nat) :
    weight completedCredit 0 278 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 278 [] 18 16
    (fun code => 0) selected_278_0 direction_278.1
    direction_278.2.1 conditioned_278 code

theorem conditional_278_0 (code : Nat) :
    weight conditionalCredit 0 278 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 278 [] 18 16
    (fun code => 0) selected_278_0 direction_278.1
    direction_278.2.2 conditioned_278 code
#print axioms selected_278_0
#print axioms source_278_0
#print axioms target_278_0
#print axioms block_278_0
#print axioms completed_278_0
#print axioms conditional_278_0

theorem selected_279_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [279])) := by rfl

theorem source_279_0 (code : Nat) :
    edgeSource 0 279 code = 629856+code/6 := by rfl

theorem target_279_0 (code : Nat) :
    edgeTarget 0 279 code = 948672+code%7776 := by rfl

theorem block_279_0 :
    savedBlockClass (75*279+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_279_0 (code : Nat) :
    weight completedCredit 0 279 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 279 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_279_0 direction_279.1
    direction_279.2.1 conditioned_279 code

theorem conditional_279_0 (code : Nat) :
    weight conditionalCredit 0 279 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 279 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_279_0 direction_279.1
    direction_279.2.2 conditioned_279 code
#print axioms selected_279_0
#print axioms source_279_0
#print axioms target_279_0
#print axioms block_279_0
#print axioms completed_279_0
#print axioms conditional_279_0

theorem selected_279_26 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 26 [] ++ [279])) := by rfl

theorem source_279_26 (code : Nat) :
    edgeSource 26 279 code = 1220832+code/6 := by rfl

theorem target_279_26 (code : Nat) :
    edgeTarget 26 279 code = 948672+code%7776 := by rfl

theorem block_279_26 :
    savedBlockClass (75*279+26) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_279_26 (code : Nat) :
    weight completedCredit 26 279 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 26 279 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_279_26 direction_279.1
    direction_279.2.1 conditioned_279 code

theorem conditional_279_26 (code : Nat) :
    weight conditionalCredit 26 279 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 26 279 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_279_26 direction_279.1
    direction_279.2.2 conditioned_279 code
#print axioms selected_279_26
#print axioms source_279_26
#print axioms target_279_26
#print axioms block_279_26
#print axioms completed_279_26
#print axioms conditional_279_26

theorem selected_280_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [280])) := by rfl

theorem source_280_0 (code : Nat) :
    edgeSource 0 280 code = 629856+code/6 := by rfl

theorem target_280_0 (code : Nat) :
    edgeTarget 0 280 code = 956448+code%7776 := by rfl

theorem block_280_0 :
    savedBlockClass (75*280+0) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_280_0 (code : Nat) :
    weight completedCredit 0 280 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 280 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_280_0 direction_280.1
    direction_280.2.1 conditioned_280 code

theorem conditional_280_0 (code : Nat) :
    weight conditionalCredit 0 280 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 280 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_280_0 direction_280.1
    direction_280.2.2 conditioned_280 code
#print axioms selected_280_0
#print axioms source_280_0
#print axioms target_280_0
#print axioms block_280_0
#print axioms completed_280_0
#print axioms conditional_280_0

theorem selected_280_26 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 26 [] ++ [280])) := by rfl

theorem source_280_26 (code : Nat) :
    edgeSource 26 280 code = 1220832+code/6 := by rfl

theorem target_280_26 (code : Nat) :
    edgeTarget 26 280 code = 956448+code%7776 := by rfl

theorem block_280_26 :
    savedBlockClass (75*280+26) = some 113 ∧
    recordedClassRoot 113 = 3906 := by decide +kernel

theorem completed_280_26 (code : Nat) :
    weight completedCredit 26 280 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 26 280 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_280_26 direction_280.1
    direction_280.2.1 conditioned_280 code

theorem conditional_280_26 (code : Nat) :
    weight conditionalCredit 26 280 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 26 280 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_280_26 direction_280.1
    direction_280.2.2 conditioned_280 code
#print axioms selected_280_26
#print axioms source_280_26
#print axioms target_280_26
#print axioms block_280_26
#print axioms completed_280_26
#print axioms conditional_280_26

theorem selected_281_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [281])) := by rfl

theorem source_281_0 (code : Nat) :
    edgeSource 0 281 code = 629856+code/6 := by rfl

theorem target_281_0 (code : Nat) :
    edgeTarget 0 281 code = 1158624+code%7776 := by rfl

theorem block_281_0 :
    savedBlockClass (75*281+0) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_281_0 (code : Nat) :
    weight completedCredit 0 281 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 281 [] 0 12
    (fun code => 0) selected_281_0 direction_281.1
    direction_281.2.1 conditioned_281 code

theorem conditional_281_0 (code : Nat) :
    weight conditionalCredit 0 281 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 281 [] 0 12
    (fun code => 0) selected_281_0 direction_281.1
    direction_281.2.2 conditioned_281 code
#print axioms selected_281_0
#print axioms source_281_0
#print axioms target_281_0
#print axioms block_281_0
#print axioms completed_281_0
#print axioms conditional_281_0

theorem selected_281_26 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 26 [] ++ [281])) := by rfl

theorem source_281_26 (code : Nat) :
    edgeSource 26 281 code = 1220832+code/6 := by rfl

theorem target_281_26 (code : Nat) :
    edgeTarget 26 281 code = 1531872+code%7776 := by rfl

theorem block_281_26 :
    savedBlockClass (75*281+26) = some 31 ∧
    recordedClassRoot 31 = 2703 := by decide +kernel

theorem completed_281_26 (code : Nat) :
    weight completedCredit 26 281 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 26 281 [] 0 12
    (fun code => 0) selected_281_26 direction_281.1
    direction_281.2.1 conditioned_281 code

theorem conditional_281_26 (code : Nat) :
    weight conditionalCredit 26 281 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 26 281 [] 0 12
    (fun code => 0) selected_281_26 direction_281.1
    direction_281.2.2 conditioned_281 code
#print axioms selected_281_26
#print axioms source_281_26
#print axioms target_281_26
#print axioms block_281_26
#print axioms completed_281_26
#print axioms conditional_281_26

end Snake9.Context101
