import Direction101Group02

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_171_22 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 22 [] ++ [171])) := by rfl

theorem source_171_22 (code : Nat) :
    edgeSource 22 171 code = 1189728+code/6 := by rfl

theorem target_171_22 (code : Nat) :
    edgeTarget 22 171 code = 1485216+code%7776 := by rfl

theorem block_171_22 :
    savedBlockClass (75*171+22) = some 79 ∧
    recordedClassRoot 79 = 3544 := by decide +kernel

theorem completed_171_22 (code : Nat) :
    weight completedCredit 22 171 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 22 171 [] 0 12
    (fun code => 0) selected_171_22 direction_171.1
    direction_171.2.1 conditioned_171 code

theorem conditional_171_22 (code : Nat) :
    weight conditionalCredit 22 171 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 22 171 [] 0 12
    (fun code => 0) selected_171_22 direction_171.1
    direction_171.2.2 conditioned_171 code
#print axioms selected_171_22
#print axioms source_171_22
#print axioms target_171_22
#print axioms block_171_22
#print axioms completed_171_22
#print axioms conditional_171_22

theorem selected_171_36 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 36 [] ++ [171])) := by rfl

theorem source_171_36 (code : Nat) :
    edgeSource 36 171 code = 1298592+code/6 := by rfl

theorem target_171_36 (code : Nat) :
    edgeTarget 36 171 code = 1485216+code%7776 := by rfl

theorem block_171_36 :
    savedBlockClass (75*171+36) = some 79 ∧
    recordedClassRoot 79 = 3544 := by decide +kernel

theorem completed_171_36 (code : Nat) :
    weight completedCredit 36 171 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 36 171 [] 0 12
    (fun code => 0) selected_171_36 direction_171.1
    direction_171.2.1 conditioned_171 code

theorem conditional_171_36 (code : Nat) :
    weight conditionalCredit 36 171 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 36 171 [] 0 12
    (fun code => 0) selected_171_36 direction_171.1
    direction_171.2.2 conditioned_171 code
#print axioms selected_171_36
#print axioms source_171_36
#print axioms target_171_36
#print axioms block_171_36
#print axioms completed_171_36
#print axioms conditional_171_36

theorem selected_172_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [172])) := by rfl

theorem source_172_0 (code : Nat) :
    edgeSource 0 172 code = 381024+code/6 := by rfl

theorem target_172_0 (code : Nat) :
    edgeTarget 0 172 code = 85536+code%7776 := by rfl

theorem block_172_0 :
    savedBlockClass (75*172+0) = some 78 ∧
    recordedClassRoot 78 = 3532 := by decide +kernel

theorem completed_172_0 (code : Nat) :
    weight completedCredit 0 172 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 172 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_172_0 direction_172.1
    direction_172.2.1 conditioned_172 code

theorem conditional_172_0 (code : Nat) :
    weight conditionalCredit 0 172 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 172 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_172_0 direction_172.1
    direction_172.2.2 conditioned_172 code
#print axioms selected_172_0
#print axioms source_172_0
#print axioms target_172_0
#print axioms block_172_0
#print axioms completed_172_0
#print axioms conditional_172_0

theorem selected_172_22 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 22 [] ++ [172])) := by rfl

theorem source_172_22 (code : Nat) :
    edgeSource 22 172 code = 1189728+code/6 := by rfl

theorem target_172_22 (code : Nat) :
    edgeTarget 22 172 code = 1492992+code%7776 := by rfl

theorem block_172_22 :
    savedBlockClass (75*172+22) = some 78 ∧
    recordedClassRoot 78 = 3532 := by decide +kernel

theorem completed_172_22 (code : Nat) :
    weight completedCredit 22 172 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 22 172 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_172_22 direction_172.1
    direction_172.2.1 conditioned_172 code

theorem conditional_172_22 (code : Nat) :
    weight conditionalCredit 22 172 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 22 172 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_172_22 direction_172.1
    direction_172.2.2 conditioned_172 code
#print axioms selected_172_22
#print axioms source_172_22
#print axioms target_172_22
#print axioms block_172_22
#print axioms completed_172_22
#print axioms conditional_172_22

theorem selected_172_36 :
    [rule013] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 36 [] ++ [172])) := by rfl

theorem source_172_36 (code : Nat) :
    edgeSource 36 172 code = 1298592+code/6 := by rfl

theorem target_172_36 (code : Nat) :
    edgeTarget 36 172 code = 1492992+code%7776 := by rfl

theorem block_172_36 :
    savedBlockClass (75*172+36) = some 78 ∧
    recordedClassRoot 78 = 3532 := by decide +kernel

theorem completed_172_36 (code : Nat) :
    weight completedCredit 36 172 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule013] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 36 172 [rule013] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_172_36 direction_172.1
    direction_172.2.1 conditioned_172 code

theorem conditional_172_36 (code : Nat) :
    weight conditionalCredit 36 172 code =
      120*(code%6+1)+max (max 5 (emittedCredit [rule013] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 36 172 [rule013] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_172_36 direction_172.1
    direction_172.2.2 conditioned_172 code
#print axioms selected_172_36
#print axioms source_172_36
#print axioms target_172_36
#print axioms block_172_36
#print axioms completed_172_36
#print axioms conditional_172_36

theorem selected_173_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [173])) := by rfl

theorem source_173_0 (code : Nat) :
    edgeSource 0 173 code = 388800+code/6 := by rfl

theorem target_173_0 (code : Nat) :
    edgeTarget 0 173 code = 108864+code%7776 := by rfl

theorem block_173_0 :
    savedBlockClass (75*173+0) = some 80 ∧
    recordedClassRoot 80 = 3553 := by decide +kernel

theorem completed_173_0 (code : Nat) :
    weight completedCredit 0 173 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 173 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_173_0 direction_173.1
    direction_173.2.1 conditioned_173 code

theorem conditional_173_0 (code : Nat) :
    weight conditionalCredit 0 173 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 173 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_173_0 direction_173.1
    direction_173.2.2 conditioned_173 code
#print axioms selected_173_0
#print axioms source_173_0
#print axioms target_173_0
#print axioms block_173_0
#print axioms completed_173_0
#print axioms conditional_173_0

theorem selected_173_69 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 69 [] ++ [173])) := by rfl

theorem source_173_69 (code : Nat) :
    edgeSource 69 173 code = 1555200+code/6 := by rfl

theorem target_173_69 (code : Nat) :
    edgeTarget 69 173 code = 108864+code%7776 := by rfl

theorem block_173_69 :
    savedBlockClass (75*173+69) = some 80 ∧
    recordedClassRoot 80 = 3553 := by decide +kernel

theorem completed_173_69 (code : Nat) :
    weight completedCredit 69 173 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 69 173 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_173_69 direction_173.1
    direction_173.2.1 conditioned_173 code

theorem conditional_173_69 (code : Nat) :
    weight conditionalCredit 69 173 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 69 173 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_173_69 direction_173.1
    direction_173.2.2 conditioned_173 code
#print axioms selected_173_69
#print axioms source_173_69
#print axioms target_173_69
#print axioms block_173_69
#print axioms completed_173_69
#print axioms conditional_173_69

theorem selected_174_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [174])) := by rfl

theorem source_174_0 (code : Nat) :
    edgeSource 0 174 code = 388800+code/6 := by rfl

theorem target_174_0 (code : Nat) :
    edgeTarget 0 174 code = 93312+code%7776 := by rfl

theorem block_174_0 :
    savedBlockClass (75*174+0) = some 81 ∧
    recordedClassRoot 81 = 3562 := by decide +kernel

theorem completed_174_0 (code : Nat) :
    weight completedCredit 0 174 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 174 [] 0 16
    (fun code => 0) selected_174_0 direction_174.1
    direction_174.2.1 conditioned_174 code

theorem conditional_174_0 (code : Nat) :
    weight conditionalCredit 0 174 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 174 [] 0 16
    (fun code => 0) selected_174_0 direction_174.1
    direction_174.2.2 conditioned_174 code
#print axioms selected_174_0
#print axioms source_174_0
#print axioms target_174_0
#print axioms block_174_0
#print axioms completed_174_0
#print axioms conditional_174_0

theorem selected_174_69 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 69 [] ++ [174])) := by rfl

theorem source_174_69 (code : Nat) :
    edgeSource 69 174 code = 1555200+code/6 := by rfl

theorem target_174_69 (code : Nat) :
    edgeTarget 69 174 code = 93312+code%7776 := by rfl

theorem block_174_69 :
    savedBlockClass (75*174+69) = some 81 ∧
    recordedClassRoot 81 = 3562 := by decide +kernel

theorem completed_174_69 (code : Nat) :
    weight completedCredit 69 174 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 69 174 [] 0 16
    (fun code => 0) selected_174_69 direction_174.1
    direction_174.2.1 conditioned_174 code

theorem conditional_174_69 (code : Nat) :
    weight conditionalCredit 69 174 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 69 174 [] 0 16
    (fun code => 0) selected_174_69 direction_174.1
    direction_174.2.2 conditioned_174 code
#print axioms selected_174_69
#print axioms source_174_69
#print axioms target_174_69
#print axioms block_174_69
#print axioms completed_174_69
#print axioms conditional_174_69

theorem selected_175_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [175])) := by rfl

theorem source_175_0 (code : Nat) :
    edgeSource 0 175 code = 388800+code/6 := by rfl

theorem target_175_0 (code : Nat) :
    edgeTarget 0 175 code = 1104192+code%7776 := by rfl

theorem block_175_0 :
    savedBlockClass (75*175+0) = some 82 ∧
    recordedClassRoot 82 = 3571 := by decide +kernel

theorem completed_175_0 (code : Nat) :
    weight completedCredit 0 175 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 175 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_175_0 direction_175.1
    direction_175.2.1 conditioned_175 code

theorem conditional_175_0 (code : Nat) :
    weight conditionalCredit 0 175 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 175 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_175_0 direction_175.1
    direction_175.2.2 conditioned_175 code
#print axioms selected_175_0
#print axioms source_175_0
#print axioms target_175_0
#print axioms block_175_0
#print axioms completed_175_0
#print axioms conditional_175_0

theorem selected_175_69 :
    [rule046] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 69 [] ++ [175])) := by rfl

theorem source_175_69 (code : Nat) :
    edgeSource 69 175 code = 1555200+code/6 := by rfl

theorem target_175_69 (code : Nat) :
    edgeTarget 69 175 code = 1104192+code%7776 := by rfl

theorem block_175_69 :
    savedBlockClass (75*175+69) = some 82 ∧
    recordedClassRoot 82 = 3571 := by decide +kernel

theorem completed_175_69 (code : Nat) :
    weight completedCredit 69 175 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule046] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 69 175 [rule046] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_175_69 direction_175.1
    direction_175.2.1 conditioned_175 code

theorem conditional_175_69 (code : Nat) :
    weight conditionalCredit 69 175 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule046] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 69 175 [rule046] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_175_69 direction_175.1
    direction_175.2.2 conditioned_175 code
#print axioms selected_175_69
#print axioms source_175_69
#print axioms target_175_69
#print axioms block_175_69
#print axioms completed_175_69
#print axioms conditional_175_69

theorem selected_176_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [176])) := by rfl

theorem source_176_0 (code : Nat) :
    edgeSource 0 176 code = 396576+code/6 := by rfl

theorem target_176_0 (code : Nat) :
    edgeTarget 0 176 code = 139968+code%7776 := by rfl

theorem block_176_0 :
    savedBlockClass (75*176+0) = some 83 ∧
    recordedClassRoot 83 = 3579 := by decide +kernel

theorem completed_176_0 (code : Nat) :
    weight completedCredit 0 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 176 [] 12 16
    (fun code => 0) selected_176_0 direction_176.1
    direction_176.2.1 conditioned_176 code

theorem conditional_176_0 (code : Nat) :
    weight conditionalCredit 0 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 176 [] 12 16
    (fun code => 0) selected_176_0 direction_176.1
    direction_176.2.2 conditioned_176 code
#print axioms selected_176_0
#print axioms source_176_0
#print axioms target_176_0
#print axioms block_176_0
#print axioms completed_176_0
#print axioms conditional_176_0

theorem selected_176_23 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 23 [] ++ [176])) := by rfl

theorem source_176_23 (code : Nat) :
    edgeSource 23 176 code = 1197504+code/6 := by rfl

theorem target_176_23 (code : Nat) :
    edgeTarget 23 176 code = 139968+code%7776 := by rfl

theorem block_176_23 :
    savedBlockClass (75*176+23) = some 83 ∧
    recordedClassRoot 83 = 3579 := by decide +kernel

theorem completed_176_23 (code : Nat) :
    weight completedCredit 23 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 23 176 [] 12 16
    (fun code => 0) selected_176_23 direction_176.1
    direction_176.2.1 conditioned_176 code

theorem conditional_176_23 (code : Nat) :
    weight conditionalCredit 23 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 23 176 [] 12 16
    (fun code => 0) selected_176_23 direction_176.1
    direction_176.2.2 conditioned_176 code
#print axioms selected_176_23
#print axioms source_176_23
#print axioms target_176_23
#print axioms block_176_23
#print axioms completed_176_23
#print axioms conditional_176_23

theorem selected_176_43 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 43 [] ++ [176])) := by rfl

theorem source_176_43 (code : Nat) :
    edgeSource 43 176 code = 1353024+code/6 := by rfl

theorem target_176_43 (code : Nat) :
    edgeTarget 43 176 code = 139968+code%7776 := by rfl

theorem block_176_43 :
    savedBlockClass (75*176+43) = some 83 ∧
    recordedClassRoot 83 = 3579 := by decide +kernel

theorem completed_176_43 (code : Nat) :
    weight completedCredit 43 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 43 176 [] 12 16
    (fun code => 0) selected_176_43 direction_176.1
    direction_176.2.1 conditioned_176 code

theorem conditional_176_43 (code : Nat) :
    weight conditionalCredit 43 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 43 176 [] 12 16
    (fun code => 0) selected_176_43 direction_176.1
    direction_176.2.2 conditioned_176 code
#print axioms selected_176_43
#print axioms source_176_43
#print axioms target_176_43
#print axioms block_176_43
#print axioms completed_176_43
#print axioms conditional_176_43

theorem selected_176_70 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 70 [] ++ [176])) := by rfl

theorem source_176_70 (code : Nat) :
    edgeSource 70 176 code = 1562976+code/6 := by rfl

theorem target_176_70 (code : Nat) :
    edgeTarget 70 176 code = 139968+code%7776 := by rfl

theorem block_176_70 :
    savedBlockClass (75*176+70) = some 83 ∧
    recordedClassRoot 83 = 3579 := by decide +kernel

theorem completed_176_70 (code : Nat) :
    weight completedCredit 70 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 70 176 [] 12 16
    (fun code => 0) selected_176_70 direction_176.1
    direction_176.2.1 conditioned_176 code

theorem conditional_176_70 (code : Nat) :
    weight conditionalCredit 70 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 70 176 [] 12 16
    (fun code => 0) selected_176_70 direction_176.1
    direction_176.2.2 conditioned_176 code
#print axioms selected_176_70
#print axioms source_176_70
#print axioms target_176_70
#print axioms block_176_70
#print axioms completed_176_70
#print axioms conditional_176_70

theorem selected_176_72 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 72 [] ++ [176])) := by rfl

theorem source_176_72 (code : Nat) :
    edgeSource 72 176 code = 1578528+code/6 := by rfl

theorem target_176_72 (code : Nat) :
    edgeTarget 72 176 code = 139968+code%7776 := by rfl

theorem block_176_72 :
    savedBlockClass (75*176+72) = some 83 ∧
    recordedClassRoot 83 = 3579 := by decide +kernel

theorem completed_176_72 (code : Nat) :
    weight completedCredit 72 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 72 176 [] 12 16
    (fun code => 0) selected_176_72 direction_176.1
    direction_176.2.1 conditioned_176 code

theorem conditional_176_72 (code : Nat) :
    weight conditionalCredit 72 176 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 72 176 [] 12 16
    (fun code => 0) selected_176_72 direction_176.1
    direction_176.2.2 conditioned_176 code
#print axioms selected_176_72
#print axioms source_176_72
#print axioms target_176_72
#print axioms block_176_72
#print axioms completed_176_72
#print axioms conditional_176_72

theorem selected_177_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [177])) := by rfl

theorem source_177_0 (code : Nat) :
    edgeSource 0 177 code = 396576+code/6 := by rfl

theorem target_177_0 (code : Nat) :
    edgeTarget 0 177 code = 1111968+code%7776 := by rfl

theorem block_177_0 :
    savedBlockClass (75*177+0) = some 84 ∧
    recordedClassRoot 84 = 3589 := by decide +kernel

theorem completed_177_0 (code : Nat) :
    weight completedCredit 0 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 177 [] 8 0
    (fun code => 0) selected_177_0 direction_177.1
    direction_177.2.1 conditioned_177 code

theorem conditional_177_0 (code : Nat) :
    weight conditionalCredit 0 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 177 [] 8 16
    (fun code => 0) selected_177_0 direction_177.1
    direction_177.2.2 conditioned_177 code
#print axioms selected_177_0
#print axioms source_177_0
#print axioms target_177_0
#print axioms block_177_0
#print axioms completed_177_0
#print axioms conditional_177_0

theorem selected_177_23 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 23 [] ++ [177])) := by rfl

theorem source_177_23 (code : Nat) :
    edgeSource 23 177 code = 1197504+code/6 := by rfl

theorem target_177_23 (code : Nat) :
    edgeTarget 23 177 code = 1500768+code%7776 := by rfl

theorem block_177_23 :
    savedBlockClass (75*177+23) = some 84 ∧
    recordedClassRoot 84 = 3589 := by decide +kernel

theorem completed_177_23 (code : Nat) :
    weight completedCredit 23 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 23 177 [] 8 0
    (fun code => 0) selected_177_23 direction_177.1
    direction_177.2.1 conditioned_177 code

theorem conditional_177_23 (code : Nat) :
    weight conditionalCredit 23 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 23 177 [] 8 16
    (fun code => 0) selected_177_23 direction_177.1
    direction_177.2.2 conditioned_177 code
#print axioms selected_177_23
#print axioms source_177_23
#print axioms target_177_23
#print axioms block_177_23
#print axioms completed_177_23
#print axioms conditional_177_23

theorem selected_177_43 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 43 [] ++ [177])) := by rfl

theorem source_177_43 (code : Nat) :
    edgeSource 43 177 code = 1353024+code/6 := by rfl

theorem target_177_43 (code : Nat) :
    edgeTarget 43 177 code = 1500768+code%7776 := by rfl

theorem block_177_43 :
    savedBlockClass (75*177+43) = some 85 ∧
    recordedClassRoot 85 = 3690 := by decide +kernel

theorem completed_177_43 (code : Nat) :
    weight completedCredit 43 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 43 177 [] 8 0
    (fun code => 0) selected_177_43 direction_177.1
    direction_177.2.1 conditioned_177 code

theorem conditional_177_43 (code : Nat) :
    weight conditionalCredit 43 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 43 177 [] 8 16
    (fun code => 0) selected_177_43 direction_177.1
    direction_177.2.2 conditioned_177 code
#print axioms selected_177_43
#print axioms source_177_43
#print axioms target_177_43
#print axioms block_177_43
#print axioms completed_177_43
#print axioms conditional_177_43

theorem selected_177_70 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 70 [] ++ [177])) := by rfl

theorem source_177_70 (code : Nat) :
    edgeSource 70 177 code = 1562976+code/6 := by rfl

theorem target_177_70 (code : Nat) :
    edgeTarget 70 177 code = 1500768+code%7776 := by rfl

theorem block_177_70 :
    savedBlockClass (75*177+70) = some 85 ∧
    recordedClassRoot 85 = 3690 := by decide +kernel

theorem completed_177_70 (code : Nat) :
    weight completedCredit 70 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 70 177 [] 8 0
    (fun code => 0) selected_177_70 direction_177.1
    direction_177.2.1 conditioned_177 code

theorem conditional_177_70 (code : Nat) :
    weight conditionalCredit 70 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 70 177 [] 8 16
    (fun code => 0) selected_177_70 direction_177.1
    direction_177.2.2 conditioned_177 code
#print axioms selected_177_70
#print axioms source_177_70
#print axioms target_177_70
#print axioms block_177_70
#print axioms completed_177_70
#print axioms conditional_177_70

theorem selected_177_72 :
    [rule051] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 72 [] ++ [177])) := by rfl

theorem source_177_72 (code : Nat) :
    edgeSource 72 177 code = 1578528+code/6 := by rfl

theorem target_177_72 (code : Nat) :
    edgeTarget 72 177 code = 1500768+code%7776 := by rfl

theorem block_177_72 :
    savedBlockClass (75*177+72) = some 84 ∧
    recordedClassRoot 84 = 3589 := by decide +kernel

theorem completed_177_72 (code : Nat) :
    weight completedCredit 72 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [rule051] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 72 177 [rule051] 8 0
    (fun code => 0) selected_177_72 direction_177.1
    direction_177.2.1 conditioned_177 code

theorem conditional_177_72 (code : Nat) :
    weight conditionalCredit 72 177 code =
      120*(code%6+1)+max (max 8 (emittedCredit [rule051] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 72 177 [rule051] 8 16
    (fun code => 0) selected_177_72 direction_177.1
    direction_177.2.2 conditioned_177 code
#print axioms selected_177_72
#print axioms source_177_72
#print axioms target_177_72
#print axioms block_177_72
#print axioms completed_177_72
#print axioms conditional_177_72

theorem selected_178_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [178])) := by rfl

theorem source_178_0 (code : Nat) :
    edgeSource 0 178 code = 396576+code/6 := by rfl

theorem target_178_0 (code : Nat) :
    edgeTarget 0 178 code = 147744+code%7776 := by rfl

theorem block_178_0 :
    savedBlockClass (75*178+0) = some 86 ∧
    recordedClassRoot 86 = 3698 := by decide +kernel

theorem completed_178_0 (code : Nat) :
    weight completedCredit 0 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 178 [] 20 16
    (fun code => 0) selected_178_0 direction_178.1
    direction_178.2.1 conditioned_178 code

theorem conditional_178_0 (code : Nat) :
    weight conditionalCredit 0 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 178 [] 20 16
    (fun code => 0) selected_178_0 direction_178.1
    direction_178.2.2 conditioned_178 code
#print axioms selected_178_0
#print axioms source_178_0
#print axioms target_178_0
#print axioms block_178_0
#print axioms completed_178_0
#print axioms conditional_178_0

theorem selected_178_23 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 23 [] ++ [178])) := by rfl

theorem source_178_23 (code : Nat) :
    edgeSource 23 178 code = 1197504+code/6 := by rfl

theorem target_178_23 (code : Nat) :
    edgeTarget 23 178 code = 147744+code%7776 := by rfl

theorem block_178_23 :
    savedBlockClass (75*178+23) = some 86 ∧
    recordedClassRoot 86 = 3698 := by decide +kernel

theorem completed_178_23 (code : Nat) :
    weight completedCredit 23 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 23 178 [] 20 16
    (fun code => 0) selected_178_23 direction_178.1
    direction_178.2.1 conditioned_178 code

theorem conditional_178_23 (code : Nat) :
    weight conditionalCredit 23 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 23 178 [] 20 16
    (fun code => 0) selected_178_23 direction_178.1
    direction_178.2.2 conditioned_178 code
#print axioms selected_178_23
#print axioms source_178_23
#print axioms target_178_23
#print axioms block_178_23
#print axioms completed_178_23
#print axioms conditional_178_23

theorem selected_178_43 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 43 [] ++ [178])) := by rfl

theorem source_178_43 (code : Nat) :
    edgeSource 43 178 code = 1353024+code/6 := by rfl

theorem target_178_43 (code : Nat) :
    edgeTarget 43 178 code = 147744+code%7776 := by rfl

theorem block_178_43 :
    savedBlockClass (75*178+43) = some 86 ∧
    recordedClassRoot 86 = 3698 := by decide +kernel

theorem completed_178_43 (code : Nat) :
    weight completedCredit 43 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 43 178 [] 20 16
    (fun code => 0) selected_178_43 direction_178.1
    direction_178.2.1 conditioned_178 code

theorem conditional_178_43 (code : Nat) :
    weight conditionalCredit 43 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 43 178 [] 20 16
    (fun code => 0) selected_178_43 direction_178.1
    direction_178.2.2 conditioned_178 code
#print axioms selected_178_43
#print axioms source_178_43
#print axioms target_178_43
#print axioms block_178_43
#print axioms completed_178_43
#print axioms conditional_178_43

theorem selected_178_70 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 70 [] ++ [178])) := by rfl

theorem source_178_70 (code : Nat) :
    edgeSource 70 178 code = 1562976+code/6 := by rfl

theorem target_178_70 (code : Nat) :
    edgeTarget 70 178 code = 147744+code%7776 := by rfl

theorem block_178_70 :
    savedBlockClass (75*178+70) = some 86 ∧
    recordedClassRoot 86 = 3698 := by decide +kernel

theorem completed_178_70 (code : Nat) :
    weight completedCredit 70 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 70 178 [] 20 16
    (fun code => 0) selected_178_70 direction_178.1
    direction_178.2.1 conditioned_178 code

theorem conditional_178_70 (code : Nat) :
    weight conditionalCredit 70 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 70 178 [] 20 16
    (fun code => 0) selected_178_70 direction_178.1
    direction_178.2.2 conditioned_178 code
#print axioms selected_178_70
#print axioms source_178_70
#print axioms target_178_70
#print axioms block_178_70
#print axioms completed_178_70
#print axioms conditional_178_70

theorem selected_178_72 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 72 [] ++ [178])) := by rfl

theorem source_178_72 (code : Nat) :
    edgeSource 72 178 code = 1578528+code/6 := by rfl

theorem target_178_72 (code : Nat) :
    edgeTarget 72 178 code = 147744+code%7776 := by rfl

theorem block_178_72 :
    savedBlockClass (75*178+72) = some 86 ∧
    recordedClassRoot 86 = 3698 := by decide +kernel

theorem completed_178_72 (code : Nat) :
    weight completedCredit 72 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 72 178 [] 20 16
    (fun code => 0) selected_178_72 direction_178.1
    direction_178.2.1 conditioned_178 code

theorem conditional_178_72 (code : Nat) :
    weight conditionalCredit 72 178 code =
      120*(code%6+1)+max (max 20 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 72 178 [] 20 16
    (fun code => 0) selected_178_72 direction_178.1
    direction_178.2.2 conditioned_178 code
#print axioms selected_178_72
#print axioms source_178_72
#print axioms target_178_72
#print axioms block_178_72
#print axioms completed_178_72
#print axioms conditional_178_72

theorem selected_179_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [179])) := by rfl

theorem source_179_0 (code : Nat) :
    edgeSource 0 179 code = 404352+code/6 := by rfl

theorem target_179_0 (code : Nat) :
    edgeTarget 0 179 code = 178848+code%7776 := by rfl

theorem block_179_0 :
    savedBlockClass (75*179+0) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_0 (code : Nat) :
    weight completedCredit 0 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_0 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_0 (code : Nat) :
    weight conditionalCredit 0 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_0 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_0
#print axioms source_179_0
#print axioms target_179_0
#print axioms block_179_0
#print axioms completed_179_0
#print axioms conditional_179_0

theorem selected_179_21 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 21 [] ++ [179])) := by rfl

theorem source_179_21 (code : Nat) :
    edgeSource 21 179 code = 1181952+code/6 := by rfl

theorem target_179_21 (code : Nat) :
    edgeTarget 21 179 code = 178848+code%7776 := by rfl

theorem block_179_21 :
    savedBlockClass (75*179+21) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_21 (code : Nat) :
    weight completedCredit 21 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 21 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_21 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_21 (code : Nat) :
    weight conditionalCredit 21 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 21 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_21 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_21
#print axioms source_179_21
#print axioms target_179_21
#print axioms block_179_21
#print axioms completed_179_21
#print axioms conditional_179_21

theorem selected_179_24 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 24 [] ++ [179])) := by rfl

theorem source_179_24 (code : Nat) :
    edgeSource 24 179 code = 1205280+code/6 := by rfl

theorem target_179_24 (code : Nat) :
    edgeTarget 24 179 code = 178848+code%7776 := by rfl

theorem block_179_24 :
    savedBlockClass (75*179+24) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_24 (code : Nat) :
    weight completedCredit 24 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 24 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_24 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_24 (code : Nat) :
    weight conditionalCredit 24 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 24 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_24 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_24
#print axioms source_179_24
#print axioms target_179_24
#print axioms block_179_24
#print axioms completed_179_24
#print axioms conditional_179_24

theorem selected_179_35 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 35 [] ++ [179])) := by rfl

theorem source_179_35 (code : Nat) :
    edgeSource 35 179 code = 1290816+code/6 := by rfl

theorem target_179_35 (code : Nat) :
    edgeTarget 35 179 code = 178848+code%7776 := by rfl

theorem block_179_35 :
    savedBlockClass (75*179+35) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_35 (code : Nat) :
    weight completedCredit 35 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 35 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_35 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_35 (code : Nat) :
    weight conditionalCredit 35 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 35 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_35 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_35
#print axioms source_179_35
#print axioms target_179_35
#print axioms block_179_35
#print axioms completed_179_35
#print axioms conditional_179_35

theorem selected_179_42 :
    [rule019] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 42 [] ++ [179])) := by rfl

theorem source_179_42 (code : Nat) :
    edgeSource 42 179 code = 1345248+code/6 := by rfl

theorem target_179_42 (code : Nat) :
    edgeTarget 42 179 code = 178848+code%7776 := by rfl

theorem block_179_42 :
    savedBlockClass (75*179+42) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_42 (code : Nat) :
    weight completedCredit 42 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule019] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 42 179 [rule019] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_42 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_42 (code : Nat) :
    weight conditionalCredit 42 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule019] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 42 179 [rule019] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_42 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_42
#print axioms source_179_42
#print axioms target_179_42
#print axioms block_179_42
#print axioms completed_179_42
#print axioms conditional_179_42

theorem selected_179_52 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 52 [] ++ [179])) := by rfl

theorem source_179_52 (code : Nat) :
    edgeSource 52 179 code = 1423008+code/6 := by rfl

theorem target_179_52 (code : Nat) :
    edgeTarget 52 179 code = 178848+code%7776 := by rfl

theorem block_179_52 :
    savedBlockClass (75*179+52) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_52 (code : Nat) :
    weight completedCredit 52 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 52 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_52 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_52 (code : Nat) :
    weight conditionalCredit 52 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 52 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_52 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_52
#print axioms source_179_52
#print axioms target_179_52
#print axioms block_179_52
#print axioms completed_179_52
#print axioms conditional_179_52

theorem selected_179_53 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 53 [] ++ [179])) := by rfl

theorem source_179_53 (code : Nat) :
    edgeSource 53 179 code = 1430784+code/6 := by rfl

theorem target_179_53 (code : Nat) :
    edgeTarget 53 179 code = 178848+code%7776 := by rfl

theorem block_179_53 :
    savedBlockClass (75*179+53) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_53 (code : Nat) :
    weight completedCredit 53 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 53 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_53 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_53 (code : Nat) :
    weight conditionalCredit 53 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 53 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_53 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_53
#print axioms source_179_53
#print axioms target_179_53
#print axioms block_179_53
#print axioms completed_179_53
#print axioms conditional_179_53

theorem selected_179_68 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 68 [] ++ [179])) := by rfl

theorem source_179_68 (code : Nat) :
    edgeSource 68 179 code = 1547424+code/6 := by rfl

theorem target_179_68 (code : Nat) :
    edgeTarget 68 179 code = 178848+code%7776 := by rfl

theorem block_179_68 :
    savedBlockClass (75*179+68) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_68 (code : Nat) :
    weight completedCredit 68 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 68 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_68 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_68 (code : Nat) :
    weight conditionalCredit 68 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 68 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_68 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_68
#print axioms source_179_68
#print axioms target_179_68
#print axioms block_179_68
#print axioms completed_179_68
#print axioms conditional_179_68

theorem selected_179_71 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 71 [] ++ [179])) := by rfl

theorem source_179_71 (code : Nat) :
    edgeSource 71 179 code = 1570752+code/6 := by rfl

theorem target_179_71 (code : Nat) :
    edgeTarget 71 179 code = 178848+code%7776 := by rfl

theorem block_179_71 :
    savedBlockClass (75*179+71) = some 87 ∧
    recordedClassRoot 87 = 3706 := by decide +kernel

theorem completed_179_71 (code : Nat) :
    weight completedCredit 71 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 71 179 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_71 direction_179.1
    direction_179.2.1 conditioned_179 code

theorem conditional_179_71 (code : Nat) :
    weight conditionalCredit 71 179 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 71 179 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_179_71 direction_179.1
    direction_179.2.2 conditioned_179 code
#print axioms selected_179_71
#print axioms source_179_71
#print axioms target_179_71
#print axioms block_179_71
#print axioms completed_179_71
#print axioms conditional_179_71

theorem selected_180_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [180])) := by rfl

theorem source_180_0 (code : Nat) :
    edgeSource 0 180 code = 404352+code/6 := by rfl

theorem target_180_0 (code : Nat) :
    edgeTarget 0 180 code = 155520+code%7776 := by rfl

theorem block_180_0 :
    savedBlockClass (75*180+0) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_0 (code : Nat) :
    weight completedCredit 0 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 180 [] 0 16
    (fun code => 0) selected_180_0 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_0 (code : Nat) :
    weight conditionalCredit 0 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 180 [] 0 16
    (fun code => 0) selected_180_0 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_0
#print axioms source_180_0
#print axioms target_180_0
#print axioms block_180_0
#print axioms completed_180_0
#print axioms conditional_180_0

theorem selected_180_21 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 21 [] ++ [180])) := by rfl

theorem source_180_21 (code : Nat) :
    edgeSource 21 180 code = 1181952+code/6 := by rfl

theorem target_180_21 (code : Nat) :
    edgeTarget 21 180 code = 155520+code%7776 := by rfl

theorem block_180_21 :
    savedBlockClass (75*180+21) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_21 (code : Nat) :
    weight completedCredit 21 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 21 180 [] 0 16
    (fun code => 0) selected_180_21 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_21 (code : Nat) :
    weight conditionalCredit 21 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 21 180 [] 0 16
    (fun code => 0) selected_180_21 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_21
#print axioms source_180_21
#print axioms target_180_21
#print axioms block_180_21
#print axioms completed_180_21
#print axioms conditional_180_21

theorem selected_180_24 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 24 [] ++ [180])) := by rfl

theorem source_180_24 (code : Nat) :
    edgeSource 24 180 code = 1205280+code/6 := by rfl

theorem target_180_24 (code : Nat) :
    edgeTarget 24 180 code = 155520+code%7776 := by rfl

theorem block_180_24 :
    savedBlockClass (75*180+24) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_24 (code : Nat) :
    weight completedCredit 24 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 24 180 [] 0 16
    (fun code => 0) selected_180_24 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_24 (code : Nat) :
    weight conditionalCredit 24 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 24 180 [] 0 16
    (fun code => 0) selected_180_24 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_24
#print axioms source_180_24
#print axioms target_180_24
#print axioms block_180_24
#print axioms completed_180_24
#print axioms conditional_180_24

theorem selected_180_35 :
    [rule012] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 35 [] ++ [180])) := by rfl

theorem source_180_35 (code : Nat) :
    edgeSource 35 180 code = 1290816+code/6 := by rfl

theorem target_180_35 (code : Nat) :
    edgeTarget 35 180 code = 155520+code%7776 := by rfl

theorem block_180_35 :
    savedBlockClass (75*180+35) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_35 (code : Nat) :
    weight completedCredit 35 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule012] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 35 180 [rule012] 0 16
    (fun code => 0) selected_180_35 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_35 (code : Nat) :
    weight conditionalCredit 35 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule012] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 35 180 [rule012] 0 16
    (fun code => 0) selected_180_35 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_35
#print axioms source_180_35
#print axioms target_180_35
#print axioms block_180_35
#print axioms completed_180_35
#print axioms conditional_180_35

theorem selected_180_42 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 42 [] ++ [180])) := by rfl

theorem source_180_42 (code : Nat) :
    edgeSource 42 180 code = 1345248+code/6 := by rfl

theorem target_180_42 (code : Nat) :
    edgeTarget 42 180 code = 155520+code%7776 := by rfl

theorem block_180_42 :
    savedBlockClass (75*180+42) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_42 (code : Nat) :
    weight completedCredit 42 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 42 180 [] 0 16
    (fun code => 0) selected_180_42 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_42 (code : Nat) :
    weight conditionalCredit 42 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 42 180 [] 0 16
    (fun code => 0) selected_180_42 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_42
#print axioms source_180_42
#print axioms target_180_42
#print axioms block_180_42
#print axioms completed_180_42
#print axioms conditional_180_42

theorem selected_180_52 :
    [rule005] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 52 [] ++ [180])) := by rfl

theorem source_180_52 (code : Nat) :
    edgeSource 52 180 code = 1423008+code/6 := by rfl

theorem target_180_52 (code : Nat) :
    edgeTarget 52 180 code = 155520+code%7776 := by rfl

theorem block_180_52 :
    savedBlockClass (75*180+52) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_52 (code : Nat) :
    weight completedCredit 52 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule005] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 52 180 [rule005] 0 16
    (fun code => 0) selected_180_52 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_52 (code : Nat) :
    weight conditionalCredit 52 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule005] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 52 180 [rule005] 0 16
    (fun code => 0) selected_180_52 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_52
#print axioms source_180_52
#print axioms target_180_52
#print axioms block_180_52
#print axioms completed_180_52
#print axioms conditional_180_52

theorem selected_180_53 :
    [rule006] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 53 [] ++ [180])) := by rfl

theorem source_180_53 (code : Nat) :
    edgeSource 53 180 code = 1430784+code/6 := by rfl

theorem target_180_53 (code : Nat) :
    edgeTarget 53 180 code = 155520+code%7776 := by rfl

theorem block_180_53 :
    savedBlockClass (75*180+53) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_53 (code : Nat) :
    weight completedCredit 53 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule006] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 53 180 [rule006] 0 16
    (fun code => 0) selected_180_53 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_53 (code : Nat) :
    weight conditionalCredit 53 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule006] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 53 180 [rule006] 0 16
    (fun code => 0) selected_180_53 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_53
#print axioms source_180_53
#print axioms target_180_53
#print axioms block_180_53
#print axioms completed_180_53
#print axioms conditional_180_53

theorem selected_180_68 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 68 [] ++ [180])) := by rfl

theorem source_180_68 (code : Nat) :
    edgeSource 68 180 code = 1547424+code/6 := by rfl

theorem target_180_68 (code : Nat) :
    edgeTarget 68 180 code = 155520+code%7776 := by rfl

theorem block_180_68 :
    savedBlockClass (75*180+68) = some 89 ∧
    recordedClassRoot 89 = 3767 := by decide +kernel

theorem completed_180_68 (code : Nat) :
    weight completedCredit 68 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 68 180 [] 0 16
    (fun code => 0) selected_180_68 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_68 (code : Nat) :
    weight conditionalCredit 68 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 68 180 [] 0 16
    (fun code => 0) selected_180_68 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_68
#print axioms source_180_68
#print axioms target_180_68
#print axioms block_180_68
#print axioms completed_180_68
#print axioms conditional_180_68

theorem selected_180_71 :
    [rule047] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 71 [] ++ [180])) := by rfl

theorem source_180_71 (code : Nat) :
    edgeSource 71 180 code = 1570752+code/6 := by rfl

theorem target_180_71 (code : Nat) :
    edgeTarget 71 180 code = 155520+code%7776 := by rfl

theorem block_180_71 :
    savedBlockClass (75*180+71) = some 88 ∧
    recordedClassRoot 88 = 3713 := by decide +kernel

theorem completed_180_71 (code : Nat) :
    weight completedCredit 71 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule047] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 71 180 [rule047] 0 16
    (fun code => 0) selected_180_71 direction_180.1
    direction_180.2.1 conditioned_180 code

theorem conditional_180_71 (code : Nat) :
    weight conditionalCredit 71 180 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule047] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 71 180 [rule047] 0 16
    (fun code => 0) selected_180_71 direction_180.1
    direction_180.2.2 conditioned_180 code
#print axioms selected_180_71
#print axioms source_180_71
#print axioms target_180_71
#print axioms block_180_71
#print axioms completed_180_71
#print axioms conditional_180_71

theorem selected_181_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [181])) := by rfl

theorem source_181_0 (code : Nat) :
    edgeSource 0 181 code = 404352+code/6 := by rfl

theorem target_181_0 (code : Nat) :
    edgeTarget 0 181 code = 163296+code%7776 := by rfl

theorem block_181_0 :
    savedBlockClass (75*181+0) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_0 (code : Nat) :
    weight completedCredit 0 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_0 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_0 (code : Nat) :
    weight conditionalCredit 0 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_0 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_0
#print axioms source_181_0
#print axioms target_181_0
#print axioms block_181_0
#print axioms completed_181_0
#print axioms conditional_181_0

theorem selected_181_21 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 21 [] ++ [181])) := by rfl

theorem source_181_21 (code : Nat) :
    edgeSource 21 181 code = 1181952+code/6 := by rfl

theorem target_181_21 (code : Nat) :
    edgeTarget 21 181 code = 1469664+code%7776 := by rfl

theorem block_181_21 :
    savedBlockClass (75*181+21) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_21 (code : Nat) :
    weight completedCredit 21 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 21 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_21 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_21 (code : Nat) :
    weight conditionalCredit 21 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 21 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_21 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_21
#print axioms source_181_21
#print axioms target_181_21
#print axioms block_181_21
#print axioms completed_181_21
#print axioms conditional_181_21

theorem selected_181_24 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 24 [] ++ [181])) := by rfl

theorem source_181_24 (code : Nat) :
    edgeSource 24 181 code = 1205280+code/6 := by rfl

theorem target_181_24 (code : Nat) :
    edgeTarget 24 181 code = 1508544+code%7776 := by rfl

theorem block_181_24 :
    savedBlockClass (75*181+24) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_24 (code : Nat) :
    weight completedCredit 24 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 24 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_24 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_24 (code : Nat) :
    weight conditionalCredit 24 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 24 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_24 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_24
#print axioms source_181_24
#print axioms target_181_24
#print axioms block_181_24
#print axioms completed_181_24
#print axioms conditional_181_24

theorem selected_181_35 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 35 [] ++ [181])) := by rfl

theorem source_181_35 (code : Nat) :
    edgeSource 35 181 code = 1290816+code/6 := by rfl

theorem target_181_35 (code : Nat) :
    edgeTarget 35 181 code = 1469664+code%7776 := by rfl

theorem block_181_35 :
    savedBlockClass (75*181+35) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_35 (code : Nat) :
    weight completedCredit 35 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 35 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_35 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_35 (code : Nat) :
    weight conditionalCredit 35 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 35 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_35 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_35
#print axioms source_181_35
#print axioms target_181_35
#print axioms block_181_35
#print axioms completed_181_35
#print axioms conditional_181_35

theorem selected_181_42 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 42 [] ++ [181])) := by rfl

theorem source_181_42 (code : Nat) :
    edgeSource 42 181 code = 1345248+code/6 := by rfl

theorem target_181_42 (code : Nat) :
    edgeTarget 42 181 code = 1469664+code%7776 := by rfl

theorem block_181_42 :
    savedBlockClass (75*181+42) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_42 (code : Nat) :
    weight completedCredit 42 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 42 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_42 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_42 (code : Nat) :
    weight conditionalCredit 42 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 42 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_42 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_42
#print axioms source_181_42
#print axioms target_181_42
#print axioms block_181_42
#print axioms completed_181_42
#print axioms conditional_181_42

theorem selected_181_52 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 52 [] ++ [181])) := by rfl

theorem source_181_52 (code : Nat) :
    edgeSource 52 181 code = 1423008+code/6 := by rfl

theorem target_181_52 (code : Nat) :
    edgeTarget 52 181 code = 1469664+code%7776 := by rfl

theorem block_181_52 :
    savedBlockClass (75*181+52) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_52 (code : Nat) :
    weight completedCredit 52 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 52 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_52 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_52 (code : Nat) :
    weight conditionalCredit 52 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 52 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_52 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_52
#print axioms source_181_52
#print axioms target_181_52
#print axioms block_181_52
#print axioms completed_181_52
#print axioms conditional_181_52

theorem selected_181_53 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 53 [] ++ [181])) := by rfl

theorem source_181_53 (code : Nat) :
    edgeSource 53 181 code = 1430784+code/6 := by rfl

theorem target_181_53 (code : Nat) :
    edgeTarget 53 181 code = 1508544+code%7776 := by rfl

theorem block_181_53 :
    savedBlockClass (75*181+53) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_53 (code : Nat) :
    weight completedCredit 53 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 53 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_53 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_53 (code : Nat) :
    weight conditionalCredit 53 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 53 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_53 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_53
#print axioms source_181_53
#print axioms target_181_53
#print axioms block_181_53
#print axioms completed_181_53
#print axioms conditional_181_53

theorem selected_181_68 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 68 [] ++ [181])) := by rfl

theorem source_181_68 (code : Nat) :
    edgeSource 68 181 code = 1547424+code/6 := by rfl

theorem target_181_68 (code : Nat) :
    edgeTarget 68 181 code = 1469664+code%7776 := by rfl

theorem block_181_68 :
    savedBlockClass (75*181+68) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_68 (code : Nat) :
    weight completedCredit 68 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 68 181 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_68 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_68 (code : Nat) :
    weight conditionalCredit 68 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 68 181 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_68 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_68
#print axioms source_181_68
#print axioms target_181_68
#print axioms block_181_68
#print axioms completed_181_68
#print axioms conditional_181_68

theorem selected_181_71 :
    [rule048] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 71 [] ++ [181])) := by rfl

theorem source_181_71 (code : Nat) :
    edgeSource 71 181 code = 1570752+code/6 := by rfl

theorem target_181_71 (code : Nat) :
    edgeTarget 71 181 code = 1469664+code%7776 := by rfl

theorem block_181_71 :
    savedBlockClass (75*181+71) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_181_71 (code : Nat) :
    weight completedCredit 71 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule048] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 71 181 [rule048] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_71 direction_181.1
    direction_181.2.1 conditioned_181 code

theorem conditional_181_71 (code : Nat) :
    weight conditionalCredit 71 181 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule048] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 71 181 [rule048] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_181_71 direction_181.1
    direction_181.2.2 conditioned_181 code
#print axioms selected_181_71
#print axioms source_181_71
#print axioms target_181_71
#print axioms block_181_71
#print axioms completed_181_71
#print axioms conditional_181_71

theorem selected_182_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [182])) := by rfl

theorem source_182_0 (code : Nat) :
    edgeSource 0 182 code = 404352+code/6 := by rfl

theorem target_182_0 (code : Nat) :
    edgeTarget 0 182 code = 171072+code%7776 := by rfl

theorem block_182_0 :
    savedBlockClass (75*182+0) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_0 (code : Nat) :
    weight completedCredit 0 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 182 [] 0 0
    (fun code => 0) selected_182_0 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_0 (code : Nat) :
    weight conditionalCredit 0 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 182 [] 0 16
    (fun code => 0) selected_182_0 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_0
#print axioms source_182_0
#print axioms target_182_0
#print axioms block_182_0
#print axioms completed_182_0
#print axioms conditional_182_0

theorem selected_182_21 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 21 [] ++ [182])) := by rfl

theorem source_182_21 (code : Nat) :
    edgeSource 21 182 code = 1181952+code/6 := by rfl

theorem target_182_21 (code : Nat) :
    edgeTarget 21 182 code = 1477440+code%7776 := by rfl

theorem block_182_21 :
    savedBlockClass (75*182+21) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_21 (code : Nat) :
    weight completedCredit 21 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 21 182 [] 0 0
    (fun code => 0) selected_182_21 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_21 (code : Nat) :
    weight conditionalCredit 21 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 21 182 [] 0 16
    (fun code => 0) selected_182_21 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_21
#print axioms source_182_21
#print axioms target_182_21
#print axioms block_182_21
#print axioms completed_182_21
#print axioms conditional_182_21

theorem selected_182_24 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 24 [] ++ [182])) := by rfl

theorem source_182_24 (code : Nat) :
    edgeSource 24 182 code = 1205280+code/6 := by rfl

theorem target_182_24 (code : Nat) :
    edgeTarget 24 182 code = 1516320+code%7776 := by rfl

theorem block_182_24 :
    savedBlockClass (75*182+24) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_24 (code : Nat) :
    weight completedCredit 24 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 24 182 [] 0 0
    (fun code => 0) selected_182_24 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_24 (code : Nat) :
    weight conditionalCredit 24 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 24 182 [] 0 16
    (fun code => 0) selected_182_24 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_24
#print axioms source_182_24
#print axioms target_182_24
#print axioms block_182_24
#print axioms completed_182_24
#print axioms conditional_182_24

theorem selected_182_35 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 35 [] ++ [182])) := by rfl

theorem source_182_35 (code : Nat) :
    edgeSource 35 182 code = 1290816+code/6 := by rfl

theorem target_182_35 (code : Nat) :
    edgeTarget 35 182 code = 1477440+code%7776 := by rfl

theorem block_182_35 :
    savedBlockClass (75*182+35) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_35 (code : Nat) :
    weight completedCredit 35 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 35 182 [] 0 0
    (fun code => 0) selected_182_35 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_35 (code : Nat) :
    weight conditionalCredit 35 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 35 182 [] 0 16
    (fun code => 0) selected_182_35 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_35
#print axioms source_182_35
#print axioms target_182_35
#print axioms block_182_35
#print axioms completed_182_35
#print axioms conditional_182_35

theorem selected_182_42 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 42 [] ++ [182])) := by rfl

theorem source_182_42 (code : Nat) :
    edgeSource 42 182 code = 1345248+code/6 := by rfl

theorem target_182_42 (code : Nat) :
    edgeTarget 42 182 code = 1477440+code%7776 := by rfl

theorem block_182_42 :
    savedBlockClass (75*182+42) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_42 (code : Nat) :
    weight completedCredit 42 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 42 182 [] 0 0
    (fun code => 0) selected_182_42 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_42 (code : Nat) :
    weight conditionalCredit 42 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 42 182 [] 0 16
    (fun code => 0) selected_182_42 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_42
#print axioms source_182_42
#print axioms target_182_42
#print axioms block_182_42
#print axioms completed_182_42
#print axioms conditional_182_42

theorem selected_182_52 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 52 [] ++ [182])) := by rfl

theorem source_182_52 (code : Nat) :
    edgeSource 52 182 code = 1423008+code/6 := by rfl

theorem target_182_52 (code : Nat) :
    edgeTarget 52 182 code = 1477440+code%7776 := by rfl

theorem block_182_52 :
    savedBlockClass (75*182+52) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_52 (code : Nat) :
    weight completedCredit 52 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 52 182 [] 0 0
    (fun code => 0) selected_182_52 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_52 (code : Nat) :
    weight conditionalCredit 52 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 52 182 [] 0 16
    (fun code => 0) selected_182_52 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_52
#print axioms source_182_52
#print axioms target_182_52
#print axioms block_182_52
#print axioms completed_182_52
#print axioms conditional_182_52

theorem selected_182_53 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 53 [] ++ [182])) := by rfl

theorem source_182_53 (code : Nat) :
    edgeSource 53 182 code = 1430784+code/6 := by rfl

theorem target_182_53 (code : Nat) :
    edgeTarget 53 182 code = 1516320+code%7776 := by rfl

theorem block_182_53 :
    savedBlockClass (75*182+53) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_53 (code : Nat) :
    weight completedCredit 53 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 53 182 [] 0 0
    (fun code => 0) selected_182_53 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_53 (code : Nat) :
    weight conditionalCredit 53 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 53 182 [] 0 16
    (fun code => 0) selected_182_53 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_53
#print axioms source_182_53
#print axioms target_182_53
#print axioms block_182_53
#print axioms completed_182_53
#print axioms conditional_182_53

theorem selected_182_68 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 68 [] ++ [182])) := by rfl

theorem source_182_68 (code : Nat) :
    edgeSource 68 182 code = 1547424+code/6 := by rfl

theorem target_182_68 (code : Nat) :
    edgeTarget 68 182 code = 1477440+code%7776 := by rfl

theorem block_182_68 :
    savedBlockClass (75*182+68) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_68 (code : Nat) :
    weight completedCredit 68 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 68 182 [] 0 0
    (fun code => 0) selected_182_68 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_68 (code : Nat) :
    weight conditionalCredit 68 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 68 182 [] 0 16
    (fun code => 0) selected_182_68 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_68
#print axioms source_182_68
#print axioms target_182_68
#print axioms block_182_68
#print axioms completed_182_68
#print axioms conditional_182_68

theorem selected_182_71 :
    [rule049] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 71 [] ++ [182])) := by rfl

theorem source_182_71 (code : Nat) :
    edgeSource 71 182 code = 1570752+code/6 := by rfl

theorem target_182_71 (code : Nat) :
    edgeTarget 71 182 code = 1477440+code%7776 := by rfl

theorem block_182_71 :
    savedBlockClass (75*182+71) = some 91 ∧
    recordedClassRoot 91 = 3779 := by decide +kernel

theorem completed_182_71 (code : Nat) :
    weight completedCredit 71 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule049] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 71 182 [rule049] 0 0
    (fun code => 0) selected_182_71 direction_182.1
    direction_182.2.1 conditioned_182 code

theorem conditional_182_71 (code : Nat) :
    weight conditionalCredit 71 182 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule049] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 71 182 [rule049] 0 16
    (fun code => 0) selected_182_71 direction_182.1
    direction_182.2.2 conditioned_182 code
#print axioms selected_182_71
#print axioms source_182_71
#print axioms target_182_71
#print axioms block_182_71
#print axioms completed_182_71
#print axioms conditional_182_71

theorem selected_183_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [183])) := by rfl

theorem source_183_0 (code : Nat) :
    edgeSource 0 183 code = 404352+code/6 := by rfl

theorem target_183_0 (code : Nat) :
    edgeTarget 0 183 code = 186624+code%7776 := by rfl

theorem block_183_0 :
    savedBlockClass (75*183+0) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_0 (code : Nat) :
    weight completedCredit 0 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_0 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_0 (code : Nat) :
    weight conditionalCredit 0 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_0 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_0
#print axioms source_183_0
#print axioms target_183_0
#print axioms block_183_0
#print axioms completed_183_0
#print axioms conditional_183_0

theorem selected_183_21 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 21 [] ++ [183])) := by rfl

theorem source_183_21 (code : Nat) :
    edgeSource 21 183 code = 1181952+code/6 := by rfl

theorem target_183_21 (code : Nat) :
    edgeTarget 21 183 code = 186624+code%7776 := by rfl

theorem block_183_21 :
    savedBlockClass (75*183+21) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_21 (code : Nat) :
    weight completedCredit 21 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 21 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_21 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_21 (code : Nat) :
    weight conditionalCredit 21 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 21 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_21 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_21
#print axioms source_183_21
#print axioms target_183_21
#print axioms block_183_21
#print axioms completed_183_21
#print axioms conditional_183_21

end Snake9.Context101
