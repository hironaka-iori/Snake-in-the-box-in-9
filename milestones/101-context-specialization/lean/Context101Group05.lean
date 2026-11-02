import Direction101Group02
import Direction101Group03

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem selected_183_24 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 24 [] ++ [183])) := by rfl

theorem source_183_24 (code : Nat) :
    edgeSource 24 183 code = 1205280+code/6 := by rfl

theorem target_183_24 (code : Nat) :
    edgeTarget 24 183 code = 186624+code%7776 := by rfl

theorem block_183_24 :
    savedBlockClass (75*183+24) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_24 (code : Nat) :
    weight completedCredit 24 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 24 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_24 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_24 (code : Nat) :
    weight conditionalCredit 24 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 24 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_24 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_24
#print axioms source_183_24
#print axioms target_183_24
#print axioms block_183_24
#print axioms completed_183_24
#print axioms conditional_183_24

theorem selected_183_35 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 35 [] ++ [183])) := by rfl

theorem source_183_35 (code : Nat) :
    edgeSource 35 183 code = 1290816+code/6 := by rfl

theorem target_183_35 (code : Nat) :
    edgeTarget 35 183 code = 186624+code%7776 := by rfl

theorem block_183_35 :
    savedBlockClass (75*183+35) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_35 (code : Nat) :
    weight completedCredit 35 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 35 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_35 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_35 (code : Nat) :
    weight conditionalCredit 35 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 35 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_35 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_35
#print axioms source_183_35
#print axioms target_183_35
#print axioms block_183_35
#print axioms completed_183_35
#print axioms conditional_183_35

theorem selected_183_42 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 42 [] ++ [183])) := by rfl

theorem source_183_42 (code : Nat) :
    edgeSource 42 183 code = 1345248+code/6 := by rfl

theorem target_183_42 (code : Nat) :
    edgeTarget 42 183 code = 186624+code%7776 := by rfl

theorem block_183_42 :
    savedBlockClass (75*183+42) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_42 (code : Nat) :
    weight completedCredit 42 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 42 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_42 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_42 (code : Nat) :
    weight conditionalCredit 42 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 42 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_42 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_42
#print axioms source_183_42
#print axioms target_183_42
#print axioms block_183_42
#print axioms completed_183_42
#print axioms conditional_183_42

theorem selected_183_52 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 52 [] ++ [183])) := by rfl

theorem source_183_52 (code : Nat) :
    edgeSource 52 183 code = 1423008+code/6 := by rfl

theorem target_183_52 (code : Nat) :
    edgeTarget 52 183 code = 186624+code%7776 := by rfl

theorem block_183_52 :
    savedBlockClass (75*183+52) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_52 (code : Nat) :
    weight completedCredit 52 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 52 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_52 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_52 (code : Nat) :
    weight conditionalCredit 52 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 52 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_52 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_52
#print axioms source_183_52
#print axioms target_183_52
#print axioms block_183_52
#print axioms completed_183_52
#print axioms conditional_183_52

theorem selected_183_53 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 53 [] ++ [183])) := by rfl

theorem source_183_53 (code : Nat) :
    edgeSource 53 183 code = 1430784+code/6 := by rfl

theorem target_183_53 (code : Nat) :
    edgeTarget 53 183 code = 186624+code%7776 := by rfl

theorem block_183_53 :
    savedBlockClass (75*183+53) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_53 (code : Nat) :
    weight completedCredit 53 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 53 183 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_53 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_53 (code : Nat) :
    weight conditionalCredit 53 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 53 183 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_53 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_53
#print axioms source_183_53
#print axioms target_183_53
#print axioms block_183_53
#print axioms completed_183_53
#print axioms conditional_183_53

theorem selected_183_68 :
    [rule045] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 68 [] ++ [183])) := by rfl

theorem source_183_68 (code : Nat) :
    edgeSource 68 183 code = 1547424+code/6 := by rfl

theorem target_183_68 (code : Nat) :
    edgeTarget 68 183 code = 186624+code%7776 := by rfl

theorem block_183_68 :
    savedBlockClass (75*183+68) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_68 (code : Nat) :
    weight completedCredit 68 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule045] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 68 183 [rule045] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_68 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_68 (code : Nat) :
    weight conditionalCredit 68 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule045] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 68 183 [rule045] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_68 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_68
#print axioms source_183_68
#print axioms target_183_68
#print axioms block_183_68
#print axioms completed_183_68
#print axioms conditional_183_68

theorem selected_183_71 :
    [rule050] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 71 [] ++ [183])) := by rfl

theorem source_183_71 (code : Nat) :
    edgeSource 71 183 code = 1570752+code/6 := by rfl

theorem target_183_71 (code : Nat) :
    edgeTarget 71 183 code = 186624+code%7776 := by rfl

theorem block_183_71 :
    savedBlockClass (75*183+71) = some 90 ∧
    recordedClassRoot 90 = 3772 := by decide +kernel

theorem completed_183_71 (code : Nat) :
    weight completedCredit 71 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule050] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 71 183 [rule050] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_71 direction_183.1
    direction_183.2.1 conditioned_183 code

theorem conditional_183_71 (code : Nat) :
    weight conditionalCredit 71 183 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule050] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 71 183 [rule050] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_183_71 direction_183.1
    direction_183.2.2 conditioned_183 code
#print axioms selected_183_71
#print axioms source_183_71
#print axioms target_183_71
#print axioms block_183_71
#print axioms completed_183_71
#print axioms conditional_183_71

theorem selected_184_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [184])) := by rfl

theorem source_184_0 (code : Nat) :
    edgeSource 0 184 code = 412128+code/6 := by rfl

theorem target_184_0 (code : Nat) :
    edgeTarget 0 184 code = 69984+code%7776 := by rfl

theorem block_184_0 :
    savedBlockClass (75*184+0) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_184_0 (code : Nat) :
    weight completedCredit 0 184 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 184 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_184_0 direction_184.1
    direction_184.2.1 conditioned_184 code

theorem conditional_184_0 (code : Nat) :
    weight conditionalCredit 0 184 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 184 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_184_0 direction_184.1
    direction_184.2.2 conditioned_184 code
#print axioms selected_184_0
#print axioms source_184_0
#print axioms target_184_0
#print axioms block_184_0
#print axioms completed_184_0
#print axioms conditional_184_0

theorem selected_185_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [185])) := by rfl

theorem source_185_0 (code : Nat) :
    edgeSource 0 185 code = 412128+code/6 := by rfl

theorem target_185_0 (code : Nat) :
    edgeTarget 0 185 code = 77760+code%7776 := by rfl

theorem block_185_0 :
    savedBlockClass (75*185+0) = some 93 ∧
    recordedClassRoot 93 = 3788 := by decide +kernel

theorem completed_185_0 (code : Nat) :
    weight completedCredit 0 185 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 185 [] 2 12
    (fun code => 0) selected_185_0 direction_185.1
    direction_185.2.1 conditioned_185 code

theorem conditional_185_0 (code : Nat) :
    weight conditionalCredit 0 185 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 185 [] 2 12
    (fun code => 0) selected_185_0 direction_185.1
    direction_185.2.2 conditioned_185 code
#print axioms selected_185_0
#print axioms source_185_0
#print axioms target_185_0
#print axioms block_185_0
#print axioms completed_185_0
#print axioms conditional_185_0

theorem selected_186_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [186])) := by rfl

theorem source_186_0 (code : Nat) :
    edgeSource 0 186 code = 412128+code/6 := by rfl

theorem target_186_0 (code : Nat) :
    edgeTarget 0 186 code = 85536+code%7776 := by rfl

theorem block_186_0 :
    savedBlockClass (75*186+0) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_186_0 (code : Nat) :
    weight completedCredit 0 186 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 186 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_186_0 direction_186.1
    direction_186.2.1 conditioned_186 code

theorem conditional_186_0 (code : Nat) :
    weight conditionalCredit 0 186 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 186 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_186_0 direction_186.1
    direction_186.2.2 conditioned_186 code
#print axioms selected_186_0
#print axioms source_186_0
#print axioms target_186_0
#print axioms block_186_0
#print axioms completed_186_0
#print axioms conditional_186_0

theorem selected_187_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [187])) := by rfl

theorem source_187_0 (code : Nat) :
    edgeSource 0 187 code = 419904+code/6 := by rfl

theorem target_187_0 (code : Nat) :
    edgeTarget 0 187 code = 93312+code%7776 := by rfl

theorem block_187_0 :
    savedBlockClass (75*187+0) = some 94 ∧
    recordedClassRoot 94 = 3792 := by decide +kernel

theorem completed_187_0 (code : Nat) :
    weight completedCredit 0 187 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 187 [] 6 16
    (fun code => 0) selected_187_0 direction_187.1
    direction_187.2.1 conditioned_187 code

theorem conditional_187_0 (code : Nat) :
    weight conditionalCredit 0 187 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 187 [] 6 16
    (fun code => 0) selected_187_0 direction_187.1
    direction_187.2.2 conditioned_187 code
#print axioms selected_187_0
#print axioms source_187_0
#print axioms target_187_0
#print axioms block_187_0
#print axioms completed_187_0
#print axioms conditional_187_0

theorem selected_188_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [188])) := by rfl

theorem source_188_0 (code : Nat) :
    edgeSource 0 188 code = 419904+code/6 := by rfl

theorem target_188_0 (code : Nat) :
    edgeTarget 0 188 code = 116640+code%7776 := by rfl

theorem block_188_0 :
    savedBlockClass (75*188+0) = some 95 ∧
    recordedClassRoot 95 = 3796 := by decide +kernel

theorem completed_188_0 (code : Nat) :
    weight completedCredit 0 188 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 188 [] 6 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_188_0 direction_188.1
    direction_188.2.1 conditioned_188 code

theorem conditional_188_0 (code : Nat) :
    weight conditionalCredit 0 188 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 188 [] 6 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_188_0 direction_188.1
    direction_188.2.2 conditioned_188 code
#print axioms selected_188_0
#print axioms source_188_0
#print axioms target_188_0
#print axioms block_188_0
#print axioms completed_188_0
#print axioms conditional_188_0

theorem selected_189_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [189])) := by rfl

theorem source_189_0 (code : Nat) :
    edgeSource 0 189 code = 427680+code/6 := by rfl

theorem target_189_0 (code : Nat) :
    edgeTarget 0 189 code = 124416+code%7776 := by rfl

theorem block_189_0 :
    savedBlockClass (75*189+0) = some 96 ∧
    recordedClassRoot 96 = 3801 := by decide +kernel

theorem completed_189_0 (code : Nat) :
    weight completedCredit 0 189 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 189 [] 14 0
    (fun code => 0) selected_189_0 direction_189.1
    direction_189.2.1 conditioned_189 code

theorem conditional_189_0 (code : Nat) :
    weight conditionalCredit 0 189 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 189 [] 14 16
    (fun code => 0) selected_189_0 direction_189.1
    direction_189.2.2 conditioned_189 code
#print axioms selected_189_0
#print axioms source_189_0
#print axioms target_189_0
#print axioms block_189_0
#print axioms completed_189_0
#print axioms conditional_189_0

theorem selected_190_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [190])) := by rfl

theorem source_190_0 (code : Nat) :
    edgeSource 0 190 code = 427680+code/6 := by rfl

theorem target_190_0 (code : Nat) :
    edgeTarget 0 190 code = 147744+code%7776 := by rfl

theorem block_190_0 :
    savedBlockClass (75*190+0) = some 97 ∧
    recordedClassRoot 97 = 3806 := by decide +kernel

theorem completed_190_0 (code : Nat) :
    weight completedCredit 0 190 code =
      120*(code%6+1)+max (max 26 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 190 [] 26 16
    (fun code => 0) selected_190_0 direction_190.1
    direction_190.2.1 conditioned_190 code

theorem conditional_190_0 (code : Nat) :
    weight conditionalCredit 0 190 code =
      120*(code%6+1)+max (max 26 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 190 [] 26 16
    (fun code => 0) selected_190_0 direction_190.1
    direction_190.2.2 conditioned_190 code
#print axioms selected_190_0
#print axioms source_190_0
#print axioms target_190_0
#print axioms block_190_0
#print axioms completed_190_0
#print axioms conditional_190_0

theorem selected_191_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [191])) := by rfl

theorem source_191_0 (code : Nat) :
    edgeSource 0 191 code = 435456+code/6 := by rfl

theorem target_191_0 (code : Nat) :
    edgeTarget 0 191 code = 155520+code%7776 := by rfl

theorem block_191_0 :
    savedBlockClass (75*191+0) = some 98 ∧
    recordedClassRoot 98 = 3810 := by decide +kernel

theorem completed_191_0 (code : Nat) :
    weight completedCredit 0 191 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 191 [] 2 16
    (fun code => 0) selected_191_0 direction_191.1
    direction_191.2.1 conditioned_191 code

theorem conditional_191_0 (code : Nat) :
    weight conditionalCredit 0 191 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 191 [] 2 16
    (fun code => 0) selected_191_0 direction_191.1
    direction_191.2.2 conditioned_191 code
#print axioms selected_191_0
#print axioms source_191_0
#print axioms target_191_0
#print axioms block_191_0
#print axioms completed_191_0
#print axioms conditional_191_0

theorem selected_192_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [192])) := by rfl

theorem source_192_0 (code : Nat) :
    edgeSource 0 192 code = 435456+code/6 := by rfl

theorem target_192_0 (code : Nat) :
    edgeTarget 0 192 code = 163296+code%7776 := by rfl

theorem block_192_0 :
    savedBlockClass (75*192+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_192_0 (code : Nat) :
    weight completedCredit 0 192 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 192 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_192_0 direction_192.1
    direction_192.2.1 conditioned_192 code

theorem conditional_192_0 (code : Nat) :
    weight conditionalCredit 0 192 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 192 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_192_0 direction_192.1
    direction_192.2.2 conditioned_192 code
#print axioms selected_192_0
#print axioms source_192_0
#print axioms target_192_0
#print axioms block_192_0
#print axioms completed_192_0
#print axioms conditional_192_0

theorem selected_193_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [193])) := by rfl

theorem source_193_0 (code : Nat) :
    edgeSource 0 193 code = 435456+code/6 := by rfl

theorem target_193_0 (code : Nat) :
    edgeTarget 0 193 code = 171072+code%7776 := by rfl

theorem block_193_0 :
    savedBlockClass (75*193+0) = some 100 ∧
    recordedClassRoot 100 = 3818 := by decide +kernel

theorem completed_193_0 (code : Nat) :
    weight completedCredit 0 193 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 193 [] 2 0
    (fun code => 0) selected_193_0 direction_193.1
    direction_193.2.1 conditioned_193 code

theorem conditional_193_0 (code : Nat) :
    weight conditionalCredit 0 193 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 193 [] 2 16
    (fun code => 0) selected_193_0 direction_193.1
    direction_193.2.2 conditioned_193 code
#print axioms selected_193_0
#print axioms source_193_0
#print axioms target_193_0
#print axioms block_193_0
#print axioms completed_193_0
#print axioms conditional_193_0

theorem selected_194_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [194])) := by rfl

theorem source_194_0 (code : Nat) :
    edgeSource 0 194 code = 435456+code/6 := by rfl

theorem target_194_0 (code : Nat) :
    edgeTarget 0 194 code = 178848+code%7776 := by rfl

theorem block_194_0 :
    savedBlockClass (75*194+0) = some 101 ∧
    recordedClassRoot 101 = 3823 := by decide +kernel

theorem completed_194_0 (code : Nat) :
    weight completedCredit 0 194 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 194 [] 2 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_194_0 direction_194.1
    direction_194.2.1 conditioned_194 code

theorem conditional_194_0 (code : Nat) :
    weight conditionalCredit 0 194 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 194 [] 2 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_194_0 direction_194.1
    direction_194.2.2 conditioned_194 code
#print axioms selected_194_0
#print axioms source_194_0
#print axioms target_194_0
#print axioms block_194_0
#print axioms completed_194_0
#print axioms conditional_194_0

theorem selected_195_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [195])) := by rfl

theorem source_195_0 (code : Nat) :
    edgeSource 0 195 code = 435456+code/6 := by rfl

theorem target_195_0 (code : Nat) :
    edgeTarget 0 195 code = 186624+code%7776 := by rfl

theorem block_195_0 :
    savedBlockClass (75*195+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_195_0 (code : Nat) :
    weight completedCredit 0 195 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 195 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_195_0 direction_195.1
    direction_195.2.1 conditioned_195 code

theorem conditional_195_0 (code : Nat) :
    weight conditionalCredit 0 195 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 195 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_195_0 direction_195.1
    direction_195.2.2 conditioned_195 code
#print axioms selected_195_0
#print axioms source_195_0
#print axioms target_195_0
#print axioms block_195_0
#print axioms completed_195_0
#print axioms conditional_195_0

theorem selected_196_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [196])) := by rfl

theorem source_196_0 (code : Nat) :
    edgeSource 0 196 code = 443232+code/6 := by rfl

theorem target_196_0 (code : Nat) :
    edgeTarget 0 196 code = 7776+code%7776 := by rfl

theorem block_196_0 :
    savedBlockClass (75*196+0) = some 102 ∧
    recordedClassRoot 102 = 3829 := by decide +kernel

theorem completed_196_0 (code : Nat) :
    weight completedCredit 0 196 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 196 [] 8 16
    (fun code => 0) selected_196_0 direction_196.1
    direction_196.2.1 conditioned_196 code

theorem conditional_196_0 (code : Nat) :
    weight conditionalCredit 0 196 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 196 [] 8 16
    (fun code => 0) selected_196_0 direction_196.1
    direction_196.2.2 conditioned_196 code
#print axioms selected_196_0
#print axioms source_196_0
#print axioms target_196_0
#print axioms block_196_0
#print axioms completed_196_0
#print axioms conditional_196_0

theorem selected_197_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [197])) := by rfl

theorem source_197_0 (code : Nat) :
    edgeSource 0 197 code = 443232+code/6 := by rfl

theorem target_197_0 (code : Nat) :
    edgeTarget 0 197 code = 31104+code%7776 := by rfl

theorem block_197_0 :
    savedBlockClass (75*197+0) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_197_0 (code : Nat) :
    weight completedCredit 0 197 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 197 [] 8 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_197_0 direction_197.1
    direction_197.2.1 conditioned_197 code

theorem conditional_197_0 (code : Nat) :
    weight conditionalCredit 0 197 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 197 [] 8 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_197_0 direction_197.1
    direction_197.2.2 conditioned_197 code
#print axioms selected_197_0
#print axioms source_197_0
#print axioms target_197_0
#print axioms block_197_0
#print axioms completed_197_0
#print axioms conditional_197_0

theorem selected_198_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [198])) := by rfl

theorem source_198_0 (code : Nat) :
    edgeSource 0 198 code = 451008+code/6 := by rfl

theorem target_198_0 (code : Nat) :
    edgeTarget 0 198 code = 0+code%7776 := by rfl

theorem block_198_0 :
    savedBlockClass (75*198+0) = some 104 ∧
    recordedClassRoot 104 = 3843 := by decide +kernel

theorem completed_198_0 (code : Nat) :
    weight completedCredit 0 198 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 198 [] 4 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_198_0 direction_198.1
    direction_198.2.1 conditioned_198 code

theorem conditional_198_0 (code : Nat) :
    weight conditionalCredit 0 198 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 198 [] 4 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_198_0 direction_198.1
    direction_198.2.2 conditioned_198 code
#print axioms selected_198_0
#print axioms source_198_0
#print axioms target_198_0
#print axioms block_198_0
#print axioms completed_198_0
#print axioms conditional_198_0

theorem selected_199_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [199])) := by rfl

theorem source_199_0 (code : Nat) :
    edgeSource 0 199 code = 451008+code/6 := by rfl

theorem target_199_0 (code : Nat) :
    edgeTarget 0 199 code = 0+code%7776 := by rfl

theorem block_199_0 :
    savedBlockClass (75*199+0) = some 104 ∧
    recordedClassRoot 104 = 3843 := by decide +kernel

theorem completed_199_0 (code : Nat) :
    weight completedCredit 0 199 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 199 [] 4 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_199_0 direction_199.1
    direction_199.2.1 conditioned_199 code

theorem conditional_199_0 (code : Nat) :
    weight conditionalCredit 0 199 code =
      120*(code%6+1)+max (max 4 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 199 [] 4 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_199_0 direction_199.1
    direction_199.2.2 conditioned_199 code
#print axioms selected_199_0
#print axioms source_199_0
#print axioms target_199_0
#print axioms block_199_0
#print axioms completed_199_0
#print axioms conditional_199_0

theorem selected_200_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [200])) := by rfl

theorem source_200_0 (code : Nat) :
    edgeSource 0 200 code = 458784+code/6 := by rfl

theorem target_200_0 (code : Nat) :
    edgeTarget 0 200 code = 31104+code%7776 := by rfl

theorem block_200_0 :
    savedBlockClass (75*200+0) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_200_0 (code : Nat) :
    weight completedCredit 0 200 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 200 [] 8 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_200_0 direction_200.1
    direction_200.2.1 conditioned_200 code

theorem conditional_200_0 (code : Nat) :
    weight conditionalCredit 0 200 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 200 [] 8 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_200_0 direction_200.1
    direction_200.2.2 conditioned_200 code
#print axioms selected_200_0
#print axioms source_200_0
#print axioms target_200_0
#print axioms block_200_0
#print axioms completed_200_0
#print axioms conditional_200_0

theorem selected_201_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [201])) := by rfl

theorem source_201_0 (code : Nat) :
    edgeSource 0 201 code = 458784+code/6 := by rfl

theorem target_201_0 (code : Nat) :
    edgeTarget 0 201 code = 7776+code%7776 := by rfl

theorem block_201_0 :
    savedBlockClass (75*201+0) = some 102 ∧
    recordedClassRoot 102 = 3829 := by decide +kernel

theorem completed_201_0 (code : Nat) :
    weight completedCredit 0 201 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 201 [] 8 16
    (fun code => 0) selected_201_0 direction_201.1
    direction_201.2.1 conditioned_201 code

theorem conditional_201_0 (code : Nat) :
    weight conditionalCredit 0 201 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 201 [] 8 16
    (fun code => 0) selected_201_0 direction_201.1
    direction_201.2.2 conditioned_201 code
#print axioms selected_201_0
#print axioms source_201_0
#print axioms target_201_0
#print axioms block_201_0
#print axioms completed_201_0
#print axioms conditional_201_0

theorem selected_202_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [202])) := by rfl

theorem source_202_0 (code : Nat) :
    edgeSource 0 202 code = 458784+code/6 := by rfl

theorem target_202_0 (code : Nat) :
    edgeTarget 0 202 code = 15552+code%7776 := by rfl

theorem block_202_0 :
    savedBlockClass (75*202+0) = some 37 ∧
    recordedClassRoot 37 = 2898 := by decide +kernel

theorem completed_202_0 (code : Nat) :
    weight completedCredit 0 202 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 202 [] 7 0
    (fun code => 0) selected_202_0 direction_202.1
    direction_202.2.1 conditioned_202 code

theorem conditional_202_0 (code : Nat) :
    weight conditionalCredit 0 202 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 202 [] 7 16
    (fun code => 0) selected_202_0 direction_202.1
    direction_202.2.2 conditioned_202 code
#print axioms selected_202_0
#print axioms source_202_0
#print axioms target_202_0
#print axioms block_202_0
#print axioms completed_202_0
#print axioms conditional_202_0

theorem selected_203_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [203])) := by rfl

theorem source_203_0 (code : Nat) :
    edgeSource 0 203 code = 458784+code/6 := by rfl

theorem target_203_0 (code : Nat) :
    edgeTarget 0 203 code = 23328+code%7776 := by rfl

theorem block_203_0 :
    savedBlockClass (75*203+0) = some 105 ∧
    recordedClassRoot 105 = 3849 := by decide +kernel

theorem completed_203_0 (code : Nat) :
    weight completedCredit 0 203 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 203 [] 8 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_203_0 direction_203.1
    direction_203.2.1 conditioned_203 code

theorem conditional_203_0 (code : Nat) :
    weight conditionalCredit 0 203 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 203 [] 8 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_203_0 direction_203.1
    direction_203.2.2 conditioned_203 code
#print axioms selected_203_0
#print axioms source_203_0
#print axioms target_203_0
#print axioms block_203_0
#print axioms completed_203_0
#print axioms conditional_203_0

theorem selected_204_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [204])) := by rfl

theorem source_204_0 (code : Nat) :
    edgeSource 0 204 code = 458784+code/6 := by rfl

theorem target_204_0 (code : Nat) :
    edgeTarget 0 204 code = 31104+code%7776 := by rfl

theorem block_204_0 :
    savedBlockClass (75*204+0) = some 103 ∧
    recordedClassRoot 103 = 3835 := by decide +kernel

theorem completed_204_0 (code : Nat) :
    weight completedCredit 0 204 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 204 [] 8 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_204_0 direction_204.1
    direction_204.2.1 conditioned_204 code

theorem conditional_204_0 (code : Nat) :
    weight conditionalCredit 0 204 code =
      120*(code%6+1)+max (max 8 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 204 [] 8 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_204_0 direction_204.1
    direction_204.2.2 conditioned_204 code
#print axioms selected_204_0
#print axioms source_204_0
#print axioms target_204_0
#print axioms block_204_0
#print axioms completed_204_0
#print axioms conditional_204_0

theorem selected_205_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [205])) := by rfl

theorem source_205_0 (code : Nat) :
    edgeSource 0 205 code = 466560+code/6 := by rfl

theorem target_205_0 (code : Nat) :
    edgeTarget 0 205 code = 38880+code%7776 := by rfl

theorem block_205_0 :
    savedBlockClass (75*205+0) = some 106 ∧
    recordedClassRoot 106 = 3862 := by decide +kernel

theorem completed_205_0 (code : Nat) :
    weight completedCredit 0 205 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 205 [] 5 16
    (fun code => 0) selected_205_0 direction_205.1
    direction_205.2.1 conditioned_205 code

theorem conditional_205_0 (code : Nat) :
    weight conditionalCredit 0 205 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 205 [] 5 16
    (fun code => 0) selected_205_0 direction_205.1
    direction_205.2.2 conditioned_205 code
#print axioms selected_205_0
#print axioms source_205_0
#print axioms target_205_0
#print axioms block_205_0
#print axioms completed_205_0
#print axioms conditional_205_0

theorem selected_206_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [206])) := by rfl

theorem source_206_0 (code : Nat) :
    edgeSource 0 206 code = 466560+code/6 := by rfl

theorem target_206_0 (code : Nat) :
    edgeTarget 0 206 code = 62208+code%7776 := by rfl

theorem block_206_0 :
    savedBlockClass (75*206+0) = some 107 ∧
    recordedClassRoot 107 = 3875 := by decide +kernel

theorem completed_206_0 (code : Nat) :
    weight completedCredit 0 206 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 206 [] 5 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_206_0 direction_206.1
    direction_206.2.1 conditioned_206 code

theorem conditional_206_0 (code : Nat) :
    weight conditionalCredit 0 206 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 206 [] 5 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_206_0 direction_206.1
    direction_206.2.2 conditioned_206 code
#print axioms selected_206_0
#print axioms source_206_0
#print axioms target_206_0
#print axioms block_206_0
#print axioms completed_206_0
#print axioms conditional_206_0

theorem selected_207_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [207])) := by rfl

theorem source_207_0 (code : Nat) :
    edgeSource 0 207 code = 474336+code/6 := by rfl

theorem target_207_0 (code : Nat) :
    edgeTarget 0 207 code = 62208+code%7776 := by rfl

theorem block_207_0 :
    savedBlockClass (75*207+0) = some 107 ∧
    recordedClassRoot 107 = 3875 := by decide +kernel

theorem completed_207_0 (code : Nat) :
    weight completedCredit 0 207 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 207 [] 7 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_207_0 direction_207.1
    direction_207.2.1 conditioned_207 code

theorem conditional_207_0 (code : Nat) :
    weight conditionalCredit 0 207 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 207 [] 7 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_207_0 direction_207.1
    direction_207.2.2 conditioned_207 code
#print axioms selected_207_0
#print axioms source_207_0
#print axioms target_207_0
#print axioms block_207_0
#print axioms completed_207_0
#print axioms conditional_207_0

theorem selected_208_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [208])) := by rfl

theorem source_208_0 (code : Nat) :
    edgeSource 0 208 code = 474336+code/6 := by rfl

theorem target_208_0 (code : Nat) :
    edgeTarget 0 208 code = 38880+code%7776 := by rfl

theorem block_208_0 :
    savedBlockClass (75*208+0) = some 106 ∧
    recordedClassRoot 106 = 3862 := by decide +kernel

theorem completed_208_0 (code : Nat) :
    weight completedCredit 0 208 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 208 [] 7 16
    (fun code => 0) selected_208_0 direction_208.1
    direction_208.2.1 conditioned_208 code

theorem conditional_208_0 (code : Nat) :
    weight conditionalCredit 0 208 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 208 [] 7 16
    (fun code => 0) selected_208_0 direction_208.1
    direction_208.2.2 conditioned_208 code
#print axioms selected_208_0
#print axioms source_208_0
#print axioms target_208_0
#print axioms block_208_0
#print axioms completed_208_0
#print axioms conditional_208_0

theorem selected_209_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [209])) := by rfl

theorem source_209_0 (code : Nat) :
    edgeSource 0 209 code = 474336+code/6 := by rfl

theorem target_209_0 (code : Nat) :
    edgeTarget 0 209 code = 46656+code%7776 := by rfl

theorem block_209_0 :
    savedBlockClass (75*209+0) = some 107 ∧
    recordedClassRoot 107 = 3875 := by decide +kernel

theorem completed_209_0 (code : Nat) :
    weight completedCredit 0 209 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 209 [] 7 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_209_0 direction_209.1
    direction_209.2.1 conditioned_209 code

theorem conditional_209_0 (code : Nat) :
    weight conditionalCredit 0 209 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 209 [] 7 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_209_0 direction_209.1
    direction_209.2.2 conditioned_209 code
#print axioms selected_209_0
#print axioms source_209_0
#print axioms target_209_0
#print axioms block_209_0
#print axioms completed_209_0
#print axioms conditional_209_0

theorem selected_210_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [210])) := by rfl

theorem source_210_0 (code : Nat) :
    edgeSource 0 210 code = 474336+code/6 := by rfl

theorem target_210_0 (code : Nat) :
    edgeTarget 0 210 code = 54432+code%7776 := by rfl

theorem block_210_0 :
    savedBlockClass (75*210+0) = some 108 ∧
    recordedClassRoot 108 = 3888 := by decide +kernel

theorem completed_210_0 (code : Nat) :
    weight completedCredit 0 210 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 210 [] 0 0
    (fun code => 0) selected_210_0 direction_210.1
    direction_210.2.1 conditioned_210 code

theorem conditional_210_0 (code : Nat) :
    weight conditionalCredit 0 210 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 210 [] 0 16
    (fun code => 0) selected_210_0 direction_210.1
    direction_210.2.2 conditioned_210 code
#print axioms selected_210_0
#print axioms source_210_0
#print axioms target_210_0
#print axioms block_210_0
#print axioms completed_210_0
#print axioms conditional_210_0

theorem selected_211_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [211])) := by rfl

theorem source_211_0 (code : Nat) :
    edgeSource 0 211 code = 474336+code/6 := by rfl

theorem target_211_0 (code : Nat) :
    edgeTarget 0 211 code = 62208+code%7776 := by rfl

theorem block_211_0 :
    savedBlockClass (75*211+0) = some 107 ∧
    recordedClassRoot 107 = 3875 := by decide +kernel

theorem completed_211_0 (code : Nat) :
    weight completedCredit 0 211 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 211 [] 7 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_211_0 direction_211.1
    direction_211.2.1 conditioned_211 code

theorem conditional_211_0 (code : Nat) :
    weight conditionalCredit 0 211 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 211 [] 7 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_211_0 direction_211.1
    direction_211.2.2 conditioned_211 code
#print axioms selected_211_0
#print axioms source_211_0
#print axioms target_211_0
#print axioms block_211_0
#print axioms completed_211_0
#print axioms conditional_211_0

theorem selected_212_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [212])) := by rfl

theorem source_212_0 (code : Nat) :
    edgeSource 0 212 code = 482112+code/6 := by rfl

theorem target_212_0 (code : Nat) :
    edgeTarget 0 212 code = 155520+code%7776 := by rfl

theorem block_212_0 :
    savedBlockClass (75*212+0) = some 98 ∧
    recordedClassRoot 98 = 3810 := by decide +kernel

theorem completed_212_0 (code : Nat) :
    weight completedCredit 0 212 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 212 [] 2 16
    (fun code => 0) selected_212_0 direction_212.1
    direction_212.2.1 conditioned_212 code

theorem conditional_212_0 (code : Nat) :
    weight conditionalCredit 0 212 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 212 [] 2 16
    (fun code => 0) selected_212_0 direction_212.1
    direction_212.2.2 conditioned_212 code
#print axioms selected_212_0
#print axioms source_212_0
#print axioms target_212_0
#print axioms block_212_0
#print axioms completed_212_0
#print axioms conditional_212_0

theorem selected_212_1 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 1 [] ++ [212])) := by rfl

theorem source_212_1 (code : Nat) :
    edgeSource 1 212 code = 1026432+code/6 := by rfl

theorem target_212_1 (code : Nat) :
    edgeTarget 1 212 code = 155520+code%7776 := by rfl

theorem block_212_1 :
    savedBlockClass (75*212+1) = some 98 ∧
    recordedClassRoot 98 = 3810 := by decide +kernel

theorem completed_212_1 (code : Nat) :
    weight completedCredit 1 212 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 1 212 [] 2 16
    (fun code => 0) selected_212_1 direction_212.1
    direction_212.2.1 conditioned_212 code

theorem conditional_212_1 (code : Nat) :
    weight conditionalCredit 1 212 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 1 212 [] 2 16
    (fun code => 0) selected_212_1 direction_212.1
    direction_212.2.2 conditioned_212 code
#print axioms selected_212_1
#print axioms source_212_1
#print axioms target_212_1
#print axioms block_212_1
#print axioms completed_212_1
#print axioms conditional_212_1

theorem selected_213_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [213])) := by rfl

theorem source_213_0 (code : Nat) :
    edgeSource 0 213 code = 482112+code/6 := by rfl

theorem target_213_0 (code : Nat) :
    edgeTarget 0 213 code = 163296+code%7776 := by rfl

theorem block_213_0 :
    savedBlockClass (75*213+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_213_0 (code : Nat) :
    weight completedCredit 0 213 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 213 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_213_0 direction_213.1
    direction_213.2.1 conditioned_213 code

theorem conditional_213_0 (code : Nat) :
    weight conditionalCredit 0 213 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 213 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_213_0 direction_213.1
    direction_213.2.2 conditioned_213 code
#print axioms selected_213_0
#print axioms source_213_0
#print axioms target_213_0
#print axioms block_213_0
#print axioms completed_213_0
#print axioms conditional_213_0

theorem selected_213_1 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 1 [] ++ [213])) := by rfl

theorem source_213_1 (code : Nat) :
    edgeSource 1 213 code = 1026432+code/6 := by rfl

theorem target_213_1 (code : Nat) :
    edgeTarget 1 213 code = 163296+code%7776 := by rfl

theorem block_213_1 :
    savedBlockClass (75*213+1) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_213_1 (code : Nat) :
    weight completedCredit 1 213 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 1 213 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_213_1 direction_213.1
    direction_213.2.1 conditioned_213 code

theorem conditional_213_1 (code : Nat) :
    weight conditionalCredit 1 213 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 1 213 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_213_1 direction_213.1
    direction_213.2.2 conditioned_213 code
#print axioms selected_213_1
#print axioms source_213_1
#print axioms target_213_1
#print axioms block_213_1
#print axioms completed_213_1
#print axioms conditional_213_1

theorem selected_214_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [214])) := by rfl

theorem source_214_0 (code : Nat) :
    edgeSource 0 214 code = 482112+code/6 := by rfl

theorem target_214_0 (code : Nat) :
    edgeTarget 0 214 code = 171072+code%7776 := by rfl

theorem block_214_0 :
    savedBlockClass (75*214+0) = some 100 ∧
    recordedClassRoot 100 = 3818 := by decide +kernel

theorem completed_214_0 (code : Nat) :
    weight completedCredit 0 214 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 214 [] 2 0
    (fun code => 0) selected_214_0 direction_214.1
    direction_214.2.1 conditioned_214 code

theorem conditional_214_0 (code : Nat) :
    weight conditionalCredit 0 214 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 214 [] 2 16
    (fun code => 0) selected_214_0 direction_214.1
    direction_214.2.2 conditioned_214 code
#print axioms selected_214_0
#print axioms source_214_0
#print axioms target_214_0
#print axioms block_214_0
#print axioms completed_214_0
#print axioms conditional_214_0

theorem selected_214_1 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 1 [] ++ [214])) := by rfl

theorem source_214_1 (code : Nat) :
    edgeSource 1 214 code = 1026432+code/6 := by rfl

theorem target_214_1 (code : Nat) :
    edgeTarget 1 214 code = 171072+code%7776 := by rfl

theorem block_214_1 :
    savedBlockClass (75*214+1) = some 100 ∧
    recordedClassRoot 100 = 3818 := by decide +kernel

theorem completed_214_1 (code : Nat) :
    weight completedCredit 1 214 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 1 214 [] 2 0
    (fun code => 0) selected_214_1 direction_214.1
    direction_214.2.1 conditioned_214 code

theorem conditional_214_1 (code : Nat) :
    weight conditionalCredit 1 214 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 1 214 [] 2 16
    (fun code => 0) selected_214_1 direction_214.1
    direction_214.2.2 conditioned_214 code
#print axioms selected_214_1
#print axioms source_214_1
#print axioms target_214_1
#print axioms block_214_1
#print axioms completed_214_1
#print axioms conditional_214_1

theorem selected_215_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [215])) := by rfl

theorem source_215_0 (code : Nat) :
    edgeSource 0 215 code = 482112+code/6 := by rfl

theorem target_215_0 (code : Nat) :
    edgeTarget 0 215 code = 1119744+code%7776 := by rfl

theorem block_215_0 :
    savedBlockClass (75*215+0) = some 101 ∧
    recordedClassRoot 101 = 3823 := by decide +kernel

theorem completed_215_0 (code : Nat) :
    weight completedCredit 0 215 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 215 [] 2 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_215_0 direction_215.1
    direction_215.2.1 conditioned_215 code

theorem conditional_215_0 (code : Nat) :
    weight conditionalCredit 0 215 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 215 [] 2 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_215_0 direction_215.1
    direction_215.2.2 conditioned_215 code
#print axioms selected_215_0
#print axioms source_215_0
#print axioms target_215_0
#print axioms block_215_0
#print axioms completed_215_0
#print axioms conditional_215_0

theorem selected_215_1 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 1 [] ++ [215])) := by rfl

theorem source_215_1 (code : Nat) :
    edgeSource 1 215 code = 1026432+code/6 := by rfl

theorem target_215_1 (code : Nat) :
    edgeTarget 1 215 code = 1267488+code%7776 := by rfl

theorem block_215_1 :
    savedBlockClass (75*215+1) = some 101 ∧
    recordedClassRoot 101 = 3823 := by decide +kernel

theorem completed_215_1 (code : Nat) :
    weight completedCredit 1 215 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 1 215 [] 2 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_215_1 direction_215.1
    direction_215.2.1 conditioned_215 code

theorem conditional_215_1 (code : Nat) :
    weight conditionalCredit 1 215 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 1 215 [] 2 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_215_1 direction_215.1
    direction_215.2.2 conditioned_215 code
#print axioms selected_215_1
#print axioms source_215_1
#print axioms target_215_1
#print axioms block_215_1
#print axioms completed_215_1
#print axioms conditional_215_1

theorem selected_216_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [216])) := by rfl

theorem source_216_0 (code : Nat) :
    edgeSource 0 216 code = 482112+code/6 := by rfl

theorem target_216_0 (code : Nat) :
    edgeTarget 0 216 code = 186624+code%7776 := by rfl

theorem block_216_0 :
    savedBlockClass (75*216+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_216_0 (code : Nat) :
    weight completedCredit 0 216 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 216 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_216_0 direction_216.1
    direction_216.2.1 conditioned_216 code

theorem conditional_216_0 (code : Nat) :
    weight conditionalCredit 0 216 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 216 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_216_0 direction_216.1
    direction_216.2.2 conditioned_216 code
#print axioms selected_216_0
#print axioms source_216_0
#print axioms target_216_0
#print axioms block_216_0
#print axioms completed_216_0
#print axioms conditional_216_0

theorem selected_216_1 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 1 [] ++ [216])) := by rfl

theorem source_216_1 (code : Nat) :
    edgeSource 1 216 code = 1026432+code/6 := by rfl

theorem target_216_1 (code : Nat) :
    edgeTarget 1 216 code = 186624+code%7776 := by rfl

theorem block_216_1 :
    savedBlockClass (75*216+1) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_216_1 (code : Nat) :
    weight completedCredit 1 216 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 1 216 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_216_1 direction_216.1
    direction_216.2.1 conditioned_216 code

theorem conditional_216_1 (code : Nat) :
    weight conditionalCredit 1 216 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 1 216 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_216_1 direction_216.1
    direction_216.2.2 conditioned_216 code
#print axioms selected_216_1
#print axioms source_216_1
#print axioms target_216_1
#print axioms block_216_1
#print axioms completed_216_1
#print axioms conditional_216_1

theorem selected_217_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [217])) := by rfl

theorem source_217_0 (code : Nat) :
    edgeSource 0 217 code = 489888+code/6 := by rfl

theorem target_217_0 (code : Nat) :
    edgeTarget 0 217 code = 85536+code%7776 := by rfl

theorem block_217_0 :
    savedBlockClass (75*217+0) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_217_0 (code : Nat) :
    weight completedCredit 0 217 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 217 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_217_0 direction_217.1
    direction_217.2.1 conditioned_217 code

theorem conditional_217_0 (code : Nat) :
    weight conditionalCredit 0 217 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 217 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_217_0 direction_217.1
    direction_217.2.2 conditioned_217 code
#print axioms selected_217_0
#print axioms source_217_0
#print axioms target_217_0
#print axioms block_217_0
#print axioms completed_217_0
#print axioms conditional_217_0

theorem selected_217_2 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 2 [] ++ [217])) := by rfl

theorem source_217_2 (code : Nat) :
    edgeSource 2 217 code = 1034208+code/6 := by rfl

theorem target_217_2 (code : Nat) :
    edgeTarget 2 217 code = 85536+code%7776 := by rfl

theorem block_217_2 :
    savedBlockClass (75*217+2) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_217_2 (code : Nat) :
    weight completedCredit 2 217 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 2 217 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_217_2 direction_217.1
    direction_217.2.1 conditioned_217 code

theorem conditional_217_2 (code : Nat) :
    weight conditionalCredit 2 217 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 2 217 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_217_2 direction_217.1
    direction_217.2.2 conditioned_217 code
#print axioms selected_217_2
#print axioms source_217_2
#print axioms target_217_2
#print axioms block_217_2
#print axioms completed_217_2
#print axioms conditional_217_2

theorem selected_218_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [218])) := by rfl

theorem source_218_0 (code : Nat) :
    edgeSource 0 218 code = 489888+code/6 := by rfl

theorem target_218_0 (code : Nat) :
    edgeTarget 0 218 code = 69984+code%7776 := by rfl

theorem block_218_0 :
    savedBlockClass (75*218+0) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_218_0 (code : Nat) :
    weight completedCredit 0 218 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 218 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_218_0 direction_218.1
    direction_218.2.1 conditioned_218 code

theorem conditional_218_0 (code : Nat) :
    weight conditionalCredit 0 218 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 218 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_218_0 direction_218.1
    direction_218.2.2 conditioned_218 code
#print axioms selected_218_0
#print axioms source_218_0
#print axioms target_218_0
#print axioms block_218_0
#print axioms completed_218_0
#print axioms conditional_218_0

theorem selected_218_2 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 2 [] ++ [218])) := by rfl

theorem source_218_2 (code : Nat) :
    edgeSource 2 218 code = 1034208+code/6 := by rfl

theorem target_218_2 (code : Nat) :
    edgeTarget 2 218 code = 69984+code%7776 := by rfl

theorem block_218_2 :
    savedBlockClass (75*218+2) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_218_2 (code : Nat) :
    weight completedCredit 2 218 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 2 218 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_218_2 direction_218.1
    direction_218.2.1 conditioned_218 code

theorem conditional_218_2 (code : Nat) :
    weight conditionalCredit 2 218 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 2 218 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_218_2 direction_218.1
    direction_218.2.2 conditioned_218 code
#print axioms selected_218_2
#print axioms source_218_2
#print axioms target_218_2
#print axioms block_218_2
#print axioms completed_218_2
#print axioms conditional_218_2

theorem selected_219_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [219])) := by rfl

theorem source_219_0 (code : Nat) :
    edgeSource 0 219 code = 489888+code/6 := by rfl

theorem target_219_0 (code : Nat) :
    edgeTarget 0 219 code = 1127520+code%7776 := by rfl

theorem block_219_0 :
    savedBlockClass (75*219+0) = some 93 ∧
    recordedClassRoot 93 = 3788 := by decide +kernel

theorem completed_219_0 (code : Nat) :
    weight completedCredit 0 219 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 219 [] 2 12
    (fun code => 0) selected_219_0 direction_219.1
    direction_219.2.1 conditioned_219 code

theorem conditional_219_0 (code : Nat) :
    weight conditionalCredit 0 219 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 219 [] 2 12
    (fun code => 0) selected_219_0 direction_219.1
    direction_219.2.2 conditioned_219 code
#print axioms selected_219_0
#print axioms source_219_0
#print axioms target_219_0
#print axioms block_219_0
#print axioms completed_219_0
#print axioms conditional_219_0

theorem selected_219_2 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 2 [] ++ [219])) := by rfl

theorem source_219_2 (code : Nat) :
    edgeSource 2 219 code = 1034208+code/6 := by rfl

theorem target_219_2 (code : Nat) :
    edgeTarget 2 219 code = 1275264+code%7776 := by rfl

theorem block_219_2 :
    savedBlockClass (75*219+2) = some 93 ∧
    recordedClassRoot 93 = 3788 := by decide +kernel

theorem completed_219_2 (code : Nat) :
    weight completedCredit 2 219 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 2 219 [] 2 12
    (fun code => 0) selected_219_2 direction_219.1
    direction_219.2.1 conditioned_219 code

theorem conditional_219_2 (code : Nat) :
    weight conditionalCredit 2 219 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 2 219 [] 2 12
    (fun code => 0) selected_219_2 direction_219.1
    direction_219.2.2 conditioned_219 code
#print axioms selected_219_2
#print axioms source_219_2
#print axioms target_219_2
#print axioms block_219_2
#print axioms completed_219_2
#print axioms conditional_219_2

theorem selected_220_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [220])) := by rfl

theorem source_220_0 (code : Nat) :
    edgeSource 0 220 code = 489888+code/6 := by rfl

theorem target_220_0 (code : Nat) :
    edgeTarget 0 220 code = 85536+code%7776 := by rfl

theorem block_220_0 :
    savedBlockClass (75*220+0) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_220_0 (code : Nat) :
    weight completedCredit 0 220 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 220 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_220_0 direction_220.1
    direction_220.2.1 conditioned_220 code

theorem conditional_220_0 (code : Nat) :
    weight conditionalCredit 0 220 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 220 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_220_0 direction_220.1
    direction_220.2.2 conditioned_220 code
#print axioms selected_220_0
#print axioms source_220_0
#print axioms target_220_0
#print axioms block_220_0
#print axioms completed_220_0
#print axioms conditional_220_0

theorem selected_220_2 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 2 [] ++ [220])) := by rfl

theorem source_220_2 (code : Nat) :
    edgeSource 2 220 code = 1034208+code/6 := by rfl

theorem target_220_2 (code : Nat) :
    edgeTarget 2 220 code = 85536+code%7776 := by rfl

theorem block_220_2 :
    savedBlockClass (75*220+2) = some 92 ∧
    recordedClassRoot 92 = 3784 := by decide +kernel

theorem completed_220_2 (code : Nat) :
    weight completedCredit 2 220 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 2 220 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_220_2 direction_220.1
    direction_220.2.1 conditioned_220 code

theorem conditional_220_2 (code : Nat) :
    weight conditionalCredit 2 220 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 2 220 [] 7 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_220_2 direction_220.1
    direction_220.2.2 conditioned_220 code
#print axioms selected_220_2
#print axioms source_220_2
#print axioms target_220_2
#print axioms block_220_2
#print axioms completed_220_2
#print axioms conditional_220_2

theorem selected_221_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [221])) := by rfl

theorem source_221_0 (code : Nat) :
    edgeSource 0 221 code = 497664+code/6 := by rfl

theorem target_221_0 (code : Nat) :
    edgeTarget 0 221 code = 116640+code%7776 := by rfl

theorem block_221_0 :
    savedBlockClass (75*221+0) = some 95 ∧
    recordedClassRoot 95 = 3796 := by decide +kernel

theorem completed_221_0 (code : Nat) :
    weight completedCredit 0 221 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 221 [] 7 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_221_0 direction_221.1
    direction_221.2.1 conditioned_221 code

theorem conditional_221_0 (code : Nat) :
    weight conditionalCredit 0 221 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 221 [] 7 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_221_0 direction_221.1
    direction_221.2.2 conditioned_221 code
#print axioms selected_221_0
#print axioms source_221_0
#print axioms target_221_0
#print axioms block_221_0
#print axioms completed_221_0
#print axioms conditional_221_0

theorem selected_222_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [222])) := by rfl

theorem source_222_0 (code : Nat) :
    edgeSource 0 222 code = 497664+code/6 := by rfl

theorem target_222_0 (code : Nat) :
    edgeTarget 0 222 code = 93312+code%7776 := by rfl

theorem block_222_0 :
    savedBlockClass (75*222+0) = some 94 ∧
    recordedClassRoot 94 = 3792 := by decide +kernel

theorem completed_222_0 (code : Nat) :
    weight completedCredit 0 222 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 222 [] 7 16
    (fun code => 0) selected_222_0 direction_222.1
    direction_222.2.1 conditioned_222 code

theorem conditional_222_0 (code : Nat) :
    weight conditionalCredit 0 222 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 222 [] 7 16
    (fun code => 0) selected_222_0 direction_222.1
    direction_222.2.2 conditioned_222 code
#print axioms selected_222_0
#print axioms source_222_0
#print axioms target_222_0
#print axioms block_222_0
#print axioms completed_222_0
#print axioms conditional_222_0

theorem selected_223_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [223])) := by rfl

theorem source_223_0 (code : Nat) :
    edgeSource 0 223 code = 497664+code/6 := by rfl

theorem target_223_0 (code : Nat) :
    edgeTarget 0 223 code = 101088+code%7776 := by rfl

theorem block_223_0 :
    savedBlockClass (75*223+0) = some 109 ∧
    recordedClassRoot 109 = 3892 := by decide +kernel

theorem completed_223_0 (code : Nat) :
    weight completedCredit 0 223 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 223 [] 2 0
    (fun code => 0) selected_223_0 direction_223.1
    direction_223.2.1 conditioned_223 code

theorem conditional_223_0 (code : Nat) :
    weight conditionalCredit 0 223 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 223 [] 2 16
    (fun code => 0) selected_223_0 direction_223.1
    direction_223.2.2 conditioned_223 code
#print axioms selected_223_0
#print axioms source_223_0
#print axioms target_223_0
#print axioms block_223_0
#print axioms completed_223_0
#print axioms conditional_223_0

theorem selected_224_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [224])) := by rfl

theorem source_224_0 (code : Nat) :
    edgeSource 0 224 code = 497664+code/6 := by rfl

theorem target_224_0 (code : Nat) :
    edgeTarget 0 224 code = 108864+code%7776 := by rfl

theorem block_224_0 :
    savedBlockClass (75*224+0) = some 110 ∧
    recordedClassRoot 110 = 3897 := by decide +kernel

theorem completed_224_0 (code : Nat) :
    weight completedCredit 0 224 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 224 [] 7 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_224_0 direction_224.1
    direction_224.2.1 conditioned_224 code

theorem conditional_224_0 (code : Nat) :
    weight conditionalCredit 0 224 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 224 [] 7 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_224_0 direction_224.1
    direction_224.2.2 conditioned_224 code
#print axioms selected_224_0
#print axioms source_224_0
#print axioms target_224_0
#print axioms block_224_0
#print axioms completed_224_0
#print axioms conditional_224_0

theorem selected_225_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [225])) := by rfl

theorem source_225_0 (code : Nat) :
    edgeSource 0 225 code = 497664+code/6 := by rfl

theorem target_225_0 (code : Nat) :
    edgeTarget 0 225 code = 116640+code%7776 := by rfl

theorem block_225_0 :
    savedBlockClass (75*225+0) = some 95 ∧
    recordedClassRoot 95 = 3796 := by decide +kernel

theorem completed_225_0 (code : Nat) :
    weight completedCredit 0 225 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 225 [] 7 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_225_0 direction_225.1
    direction_225.2.1 conditioned_225 code

theorem conditional_225_0 (code : Nat) :
    weight conditionalCredit 0 225 code =
      120*(code%6+1)+max (max 7 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 225 [] 7 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_225_0 direction_225.1
    direction_225.2.2 conditioned_225 code
#print axioms selected_225_0
#print axioms source_225_0
#print axioms target_225_0
#print axioms block_225_0
#print axioms completed_225_0
#print axioms conditional_225_0

theorem selected_226_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [226])) := by rfl

theorem source_226_0 (code : Nat) :
    edgeSource 0 226 code = 505440+code/6 := by rfl

theorem target_226_0 (code : Nat) :
    edgeTarget 0 226 code = 147744+code%7776 := by rfl

theorem block_226_0 :
    savedBlockClass (75*226+0) = some 97 ∧
    recordedClassRoot 97 = 3806 := by decide +kernel

theorem completed_226_0 (code : Nat) :
    weight completedCredit 0 226 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 226 [] 29 16
    (fun code => 0) selected_226_0 direction_226.1
    direction_226.2.1 conditioned_226 code

theorem conditional_226_0 (code : Nat) :
    weight conditionalCredit 0 226 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 226 [] 29 16
    (fun code => 0) selected_226_0 direction_226.1
    direction_226.2.2 conditioned_226 code
#print axioms selected_226_0
#print axioms source_226_0
#print axioms target_226_0
#print axioms block_226_0
#print axioms completed_226_0
#print axioms conditional_226_0

theorem selected_227_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [227])) := by rfl

theorem source_227_0 (code : Nat) :
    edgeSource 0 227 code = 505440+code/6 := by rfl

theorem target_227_0 (code : Nat) :
    edgeTarget 0 227 code = 124416+code%7776 := by rfl

theorem block_227_0 :
    savedBlockClass (75*227+0) = some 96 ∧
    recordedClassRoot 96 = 3801 := by decide +kernel

theorem completed_227_0 (code : Nat) :
    weight completedCredit 0 227 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 227 [] 17 0
    (fun code => 0) selected_227_0 direction_227.1
    direction_227.2.1 conditioned_227 code

theorem conditional_227_0 (code : Nat) :
    weight conditionalCredit 0 227 code =
      120*(code%6+1)+max (max 17 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 227 [] 17 16
    (fun code => 0) selected_227_0 direction_227.1
    direction_227.2.2 conditioned_227 code
#print axioms selected_227_0
#print axioms source_227_0
#print axioms target_227_0
#print axioms block_227_0
#print axioms completed_227_0
#print axioms conditional_227_0

theorem selected_228_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [228])) := by rfl

theorem source_228_0 (code : Nat) :
    edgeSource 0 228 code = 505440+code/6 := by rfl

theorem target_228_0 (code : Nat) :
    edgeTarget 0 228 code = 132192+code%7776 := by rfl

theorem block_228_0 :
    savedBlockClass (75*228+0) = some 97 ∧
    recordedClassRoot 97 = 3806 := by decide +kernel

theorem completed_228_0 (code : Nat) :
    weight completedCredit 0 228 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 228 [] 24 16
    (fun code => 0) selected_228_0 direction_228.1
    direction_228.2.1 conditioned_228 code

theorem conditional_228_0 (code : Nat) :
    weight conditionalCredit 0 228 code =
      120*(code%6+1)+max (max 24 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 228 [] 24 16
    (fun code => 0) selected_228_0 direction_228.1
    direction_228.2.2 conditioned_228 code
#print axioms selected_228_0
#print axioms source_228_0
#print axioms target_228_0
#print axioms block_228_0
#print axioms completed_228_0
#print axioms conditional_228_0

theorem selected_229_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [229])) := by rfl

theorem source_229_0 (code : Nat) :
    edgeSource 0 229 code = 505440+code/6 := by rfl

theorem target_229_0 (code : Nat) :
    edgeTarget 0 229 code = 139968+code%7776 := by rfl

theorem block_229_0 :
    savedBlockClass (75*229+0) = some 111 ∧
    recordedClassRoot 111 = 3902 := by decide +kernel

theorem completed_229_0 (code : Nat) :
    weight completedCredit 0 229 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 229 [] 21 16
    (fun code => 0) selected_229_0 direction_229.1
    direction_229.2.1 conditioned_229 code

theorem conditional_229_0 (code : Nat) :
    weight conditionalCredit 0 229 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 229 [] 21 16
    (fun code => 0) selected_229_0 direction_229.1
    direction_229.2.2 conditioned_229 code
#print axioms selected_229_0
#print axioms source_229_0
#print axioms target_229_0
#print axioms block_229_0
#print axioms completed_229_0
#print axioms conditional_229_0

theorem selected_230_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [230])) := by rfl

theorem source_230_0 (code : Nat) :
    edgeSource 0 230 code = 505440+code/6 := by rfl

theorem target_230_0 (code : Nat) :
    edgeTarget 0 230 code = 147744+code%7776 := by rfl

theorem block_230_0 :
    savedBlockClass (75*230+0) = some 97 ∧
    recordedClassRoot 97 = 3806 := by decide +kernel

theorem completed_230_0 (code : Nat) :
    weight completedCredit 0 230 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 230 [] 29 16
    (fun code => 0) selected_230_0 direction_230.1
    direction_230.2.1 conditioned_230 code

theorem conditional_230_0 (code : Nat) :
    weight conditionalCredit 0 230 code =
      120*(code%6+1)+max (max 29 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 230 [] 29 16
    (fun code => 0) selected_230_0 direction_230.1
    direction_230.2.2 conditioned_230 code
#print axioms selected_230_0
#print axioms source_230_0
#print axioms target_230_0
#print axioms block_230_0
#print axioms completed_230_0
#print axioms conditional_230_0

theorem selected_231_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [231])) := by rfl

theorem source_231_0 (code : Nat) :
    edgeSource 0 231 code = 513216+code/6 := by rfl

theorem target_231_0 (code : Nat) :
    edgeTarget 0 231 code = 186624+code%7776 := by rfl

theorem block_231_0 :
    savedBlockClass (75*231+0) = some 99 ∧
    recordedClassRoot 99 = 3814 := by decide +kernel

theorem completed_231_0 (code : Nat) :
    weight completedCredit 0 231 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 231 [] 2 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_231_0 direction_231.1
    direction_231.2.1 conditioned_231 code

theorem conditional_231_0 (code : Nat) :
    weight conditionalCredit 0 231 code =
      120*(code%6+1)+max (max 2 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 231 [] 2 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_231_0 direction_231.1
    direction_231.2.2 conditioned_231 code
#print axioms selected_231_0
#print axioms source_231_0
#print axioms target_231_0
#print axioms block_231_0
#print axioms completed_231_0
#print axioms conditional_231_0

end Snake9.Context101
