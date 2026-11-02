import Direction101Group01
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

theorem selected_120_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [120])) := by rfl

theorem source_120_0 (code : Nat) :
    edgeSource 0 120 code = 272160+code/6 := by rfl

theorem target_120_0 (code : Nat) :
    edgeTarget 0 120 code = 559872+code%7776 := by rfl

theorem block_120_0 :
    savedBlockClass (75*120+0) = some 56 ∧
    recordedClassRoot 56 = 3453 := by decide +kernel

theorem completed_120_0 (code : Nat) :
    weight completedCredit 0 120 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 120 [] 6 0
    (fun code => 0) selected_120_0 direction_120.1
    direction_120.2.1 conditioned_120 code

theorem conditional_120_0 (code : Nat) :
    weight conditionalCredit 0 120 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 120 [] 6 16
    (fun code => 0) selected_120_0 direction_120.1
    direction_120.2.2 conditioned_120 code
#print axioms selected_120_0
#print axioms source_120_0
#print axioms target_120_0
#print axioms block_120_0
#print axioms completed_120_0
#print axioms conditional_120_0

theorem selected_121_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [121])) := by rfl

theorem source_121_0 (code : Nat) :
    edgeSource 0 121 code = 272160+code/6 := by rfl

theorem target_121_0 (code : Nat) :
    edgeTarget 0 121 code = 575424+code%7776 := by rfl

theorem block_121_0 :
    savedBlockClass (75*121+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_121_0 (code : Nat) :
    weight completedCredit 0 121 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 121 [] 21 16
    (fun code => 0) selected_121_0 direction_121.1
    direction_121.2.1 conditioned_121 code

theorem conditional_121_0 (code : Nat) :
    weight conditionalCredit 0 121 code =
      120*(code%6+1)+max (max 21 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 121 [] 21 16
    (fun code => 0) selected_121_0 direction_121.1
    direction_121.2.2 conditioned_121 code
#print axioms selected_121_0
#print axioms source_121_0
#print axioms target_121_0
#print axioms block_121_0
#print axioms completed_121_0
#print axioms conditional_121_0

theorem selected_122_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [122])) := by rfl

theorem source_122_0 (code : Nat) :
    edgeSource 0 122 code = 279936+code/6 := by rfl

theorem target_122_0 (code : Nat) :
    edgeTarget 0 122 code = 622080+code%7776 := by rfl

theorem block_122_0 :
    savedBlockClass (75*122+0) = some 58 ∧
    recordedClassRoot 58 = 3459 := by decide +kernel

theorem completed_122_0 (code : Nat) :
    weight completedCredit 0 122 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 122 [] 0 16
    (fun code => 0) selected_122_0 direction_122.1
    direction_122.2.1 conditioned_122 code

theorem conditional_122_0 (code : Nat) :
    weight conditionalCredit 0 122 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 122 [] 0 16
    (fun code => 0) selected_122_0 direction_122.1
    direction_122.2.2 conditioned_122 code
#print axioms selected_122_0
#print axioms source_122_0
#print axioms target_122_0
#print axioms block_122_0
#print axioms completed_122_0
#print axioms conditional_122_0

theorem selected_123_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [123])) := by rfl

theorem source_123_0 (code : Nat) :
    edgeSource 0 123 code = 279936+code/6 := by rfl

theorem target_123_0 (code : Nat) :
    edgeTarget 0 123 code = 606528+code%7776 := by rfl

theorem block_123_0 :
    savedBlockClass (75*123+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_123_0 (code : Nat) :
    weight completedCredit 0 123 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 123 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_123_0 direction_123.1
    direction_123.2.1 conditioned_123 code

theorem conditional_123_0 (code : Nat) :
    weight conditionalCredit 0 123 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 123 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_123_0 direction_123.1
    direction_123.2.2 conditioned_123 code
#print axioms selected_123_0
#print axioms source_123_0
#print axioms target_123_0
#print axioms block_123_0
#print axioms completed_123_0
#print axioms conditional_123_0

theorem selected_124_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [124])) := by rfl

theorem source_124_0 (code : Nat) :
    edgeSource 0 124 code = 279936+code/6 := by rfl

theorem target_124_0 (code : Nat) :
    edgeTarget 0 124 code = 614304+code%7776 := by rfl

theorem block_124_0 :
    savedBlockClass (75*124+0) = some 60 ∧
    recordedClassRoot 60 = 3465 := by decide +kernel

theorem completed_124_0 (code : Nat) :
    weight completedCredit 0 124 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 124 [] 0 0
    (fun code => 0) selected_124_0 direction_124.1
    direction_124.2.1 conditioned_124 code

theorem conditional_124_0 (code : Nat) :
    weight conditionalCredit 0 124 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 124 [] 0 16
    (fun code => 0) selected_124_0 direction_124.1
    direction_124.2.2 conditioned_124 code
#print axioms selected_124_0
#print axioms source_124_0
#print axioms target_124_0
#print axioms block_124_0
#print axioms completed_124_0
#print axioms conditional_124_0

theorem selected_125_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [125])) := by rfl

theorem source_125_0 (code : Nat) :
    edgeSource 0 125 code = 279936+code/6 := by rfl

theorem target_125_0 (code : Nat) :
    edgeTarget 0 125 code = 629856+code%7776 := by rfl

theorem block_125_0 :
    savedBlockClass (75*125+0) = some 61 ∧
    recordedClassRoot 61 = 3469 := by decide +kernel

theorem completed_125_0 (code : Nat) :
    weight completedCredit 0 125 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 125 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_125_0 direction_125.1
    direction_125.2.1 conditioned_125 code

theorem conditional_125_0 (code : Nat) :
    weight conditionalCredit 0 125 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 125 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_125_0 direction_125.1
    direction_125.2.2 conditioned_125 code
#print axioms selected_125_0
#print axioms source_125_0
#print axioms target_125_0
#print axioms block_125_0
#print axioms completed_125_0
#print axioms conditional_125_0

theorem selected_126_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [126])) := by rfl

theorem source_126_0 (code : Nat) :
    edgeSource 0 126 code = 279936+code/6 := by rfl

theorem target_126_0 (code : Nat) :
    edgeTarget 0 126 code = 637632+code%7776 := by rfl

theorem block_126_0 :
    savedBlockClass (75*126+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_126_0 (code : Nat) :
    weight completedCredit 0 126 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 126 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_126_0 direction_126.1
    direction_126.2.1 conditioned_126 code

theorem conditional_126_0 (code : Nat) :
    weight conditionalCredit 0 126 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 126 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_126_0 direction_126.1
    direction_126.2.2 conditioned_126 code
#print axioms selected_126_0
#print axioms source_126_0
#print axioms target_126_0
#print axioms block_126_0
#print axioms completed_126_0
#print axioms conditional_126_0

theorem selected_127_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [127])) := by rfl

theorem source_127_0 (code : Nat) :
    edgeSource 0 127 code = 287712+code/6 := by rfl

theorem target_127_0 (code : Nat) :
    edgeTarget 0 127 code = 692064+code%7776 := by rfl

theorem block_127_0 :
    savedBlockClass (75*127+0) = some 62 ∧
    recordedClassRoot 62 = 3473 := by decide +kernel

theorem completed_127_0 (code : Nat) :
    weight completedCredit 0 127 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 127 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_127_0 direction_127.1
    direction_127.2.1 conditioned_127 code

theorem conditional_127_0 (code : Nat) :
    weight conditionalCredit 0 127 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 127 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_127_0 direction_127.1
    direction_127.2.2 conditioned_127 code
#print axioms selected_127_0
#print axioms source_127_0
#print axioms target_127_0
#print axioms block_127_0
#print axioms completed_127_0
#print axioms conditional_127_0

theorem selected_128_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [128])) := by rfl

theorem source_128_0 (code : Nat) :
    edgeSource 0 128 code = 287712+code/6 := by rfl

theorem target_128_0 (code : Nat) :
    edgeTarget 0 128 code = 699840+code%7776 := by rfl

theorem block_128_0 :
    savedBlockClass (75*128+0) = some 62 ∧
    recordedClassRoot 62 = 3473 := by decide +kernel

theorem completed_128_0 (code : Nat) :
    weight completedCredit 0 128 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 128 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_128_0 direction_128.1
    direction_128.2.1 conditioned_128 code

theorem conditional_128_0 (code : Nat) :
    weight conditionalCredit 0 128 code =
      120*(code%6+1)+max (max 11 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 128 [] 11 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_128_0 direction_128.1
    direction_128.2.2 conditioned_128 code
#print axioms selected_128_0
#print axioms source_128_0
#print axioms target_128_0
#print axioms block_128_0
#print axioms completed_128_0
#print axioms conditional_128_0

theorem selected_129_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [129])) := by rfl

theorem source_129_0 (code : Nat) :
    edgeSource 0 129 code = 295488+code/6 := by rfl

theorem target_129_0 (code : Nat) :
    edgeTarget 0 129 code = 653184+code%7776 := by rfl

theorem block_129_0 :
    savedBlockClass (75*129+0) = some 63 ∧
    recordedClassRoot 63 = 3476 := by decide +kernel

theorem completed_129_0 (code : Nat) :
    weight completedCredit 0 129 code =
      120*(code%6+1)+max (max 31 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 129 [] 31 16
    (fun code => 0) selected_129_0 direction_129.1
    direction_129.2.1 conditioned_129 code

theorem conditional_129_0 (code : Nat) :
    weight conditionalCredit 0 129 code =
      120*(code%6+1)+max (max 31 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 129 [] 31 16
    (fun code => 0) selected_129_0 direction_129.1
    direction_129.2.2 conditioned_129 code
#print axioms selected_129_0
#print axioms source_129_0
#print axioms target_129_0
#print axioms block_129_0
#print axioms completed_129_0
#print axioms conditional_129_0

theorem selected_130_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [130])) := by rfl

theorem source_130_0 (code : Nat) :
    edgeSource 0 130 code = 295488+code/6 := by rfl

theorem target_130_0 (code : Nat) :
    edgeTarget 0 130 code = 668736+code%7776 := by rfl

theorem block_130_0 :
    savedBlockClass (75*130+0) = some 64 ∧
    recordedClassRoot 64 = 3479 := by decide +kernel

theorem completed_130_0 (code : Nat) :
    weight completedCredit 0 130 code =
      120*(code%6+1)+max (max 42 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 130 [] 42 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_130_0 direction_130.1
    direction_130.2.1 conditioned_130 code

theorem conditional_130_0 (code : Nat) :
    weight conditionalCredit 0 130 code =
      120*(code%6+1)+max (max 42 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 130 [] 42 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_130_0 direction_130.1
    direction_130.2.2 conditioned_130 code
#print axioms selected_130_0
#print axioms source_130_0
#print axioms target_130_0
#print axioms block_130_0
#print axioms completed_130_0
#print axioms conditional_130_0

theorem selected_131_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [131])) := by rfl

theorem source_131_0 (code : Nat) :
    edgeSource 0 131 code = 303264+code/6 := by rfl

theorem target_131_0 (code : Nat) :
    edgeTarget 0 131 code = 684288+code%7776 := by rfl

theorem block_131_0 :
    savedBlockClass (75*131+0) = some 65 ∧
    recordedClassRoot 65 = 3483 := by decide +kernel

theorem completed_131_0 (code : Nat) :
    weight completedCredit 0 131 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 131 [] 6 16
    (fun code => 0) selected_131_0 direction_131.1
    direction_131.2.1 conditioned_131 code

theorem conditional_131_0 (code : Nat) :
    weight conditionalCredit 0 131 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 131 [] 6 16
    (fun code => 0) selected_131_0 direction_131.1
    direction_131.2.2 conditioned_131 code
#print axioms selected_131_0
#print axioms source_131_0
#print axioms target_131_0
#print axioms block_131_0
#print axioms completed_131_0
#print axioms conditional_131_0

theorem selected_132_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [132])) := by rfl

theorem source_132_0 (code : Nat) :
    edgeSource 0 132 code = 311040+code/6 := by rfl

theorem target_132_0 (code : Nat) :
    edgeTarget 0 132 code = 723168+code%7776 := by rfl

theorem block_132_0 :
    savedBlockClass (75*132+0) = some 63 ∧
    recordedClassRoot 63 = 3476 := by decide +kernel

theorem completed_132_0 (code : Nat) :
    weight completedCredit 0 132 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 132 [] 13 16
    (fun code => 0) selected_132_0 direction_132.1
    direction_132.2.1 conditioned_132 code

theorem conditional_132_0 (code : Nat) :
    weight conditionalCredit 0 132 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 132 [] 13 16
    (fun code => 0) selected_132_0 direction_132.1
    direction_132.2.2 conditioned_132 code
#print axioms selected_132_0
#print axioms source_132_0
#print axioms target_132_0
#print axioms block_132_0
#print axioms completed_132_0
#print axioms conditional_132_0

theorem selected_133_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [133])) := by rfl

theorem source_133_0 (code : Nat) :
    edgeSource 0 133 code = 311040+code/6 := by rfl

theorem target_133_0 (code : Nat) :
    edgeTarget 0 133 code = 707616+code%7776 := by rfl

theorem block_133_0 :
    savedBlockClass (75*133+0) = some 64 ∧
    recordedClassRoot 64 = 3479 := by decide +kernel

theorem completed_133_0 (code : Nat) :
    weight completedCredit 0 133 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 133 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_133_0 direction_133.1
    direction_133.2.1 conditioned_133 code

theorem conditional_133_0 (code : Nat) :
    weight conditionalCredit 0 133 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 133 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_133_0 direction_133.1
    direction_133.2.2 conditioned_133 code
#print axioms selected_133_0
#print axioms source_133_0
#print axioms target_133_0
#print axioms block_133_0
#print axioms completed_133_0
#print axioms conditional_133_0

theorem selected_134_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [134])) := by rfl

theorem source_134_0 (code : Nat) :
    edgeSource 0 134 code = 311040+code/6 := by rfl

theorem target_134_0 (code : Nat) :
    edgeTarget 0 134 code = 715392+code%7776 := by rfl

theorem block_134_0 :
    savedBlockClass (75*134+0) = some 66 ∧
    recordedClassRoot 66 = 3486 := by decide +kernel

theorem completed_134_0 (code : Nat) :
    weight completedCredit 0 134 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 134 [] 13 0
    (fun code => 0) selected_134_0 direction_134.1
    direction_134.2.1 conditioned_134 code

theorem conditional_134_0 (code : Nat) :
    weight conditionalCredit 0 134 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 134 [] 13 16
    (fun code => 0) selected_134_0 direction_134.1
    direction_134.2.2 conditioned_134 code
#print axioms selected_134_0
#print axioms source_134_0
#print axioms target_134_0
#print axioms block_134_0
#print axioms completed_134_0
#print axioms conditional_134_0

theorem selected_135_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [135])) := by rfl

theorem source_135_0 (code : Nat) :
    edgeSource 0 135 code = 311040+code/6 := by rfl

theorem target_135_0 (code : Nat) :
    edgeTarget 0 135 code = 730944+code%7776 := by rfl

theorem block_135_0 :
    savedBlockClass (75*135+0) = some 67 ∧
    recordedClassRoot 67 = 3489 := by decide +kernel

theorem completed_135_0 (code : Nat) :
    weight completedCredit 0 135 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 135 [] 13 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_135_0 direction_135.1
    direction_135.2.1 conditioned_135 code

theorem conditional_135_0 (code : Nat) :
    weight conditionalCredit 0 135 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 135 [] 13 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_135_0 direction_135.1
    direction_135.2.2 conditioned_135 code
#print axioms selected_135_0
#print axioms source_135_0
#print axioms target_135_0
#print axioms block_135_0
#print axioms completed_135_0
#print axioms conditional_135_0

theorem selected_136_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [136])) := by rfl

theorem source_136_0 (code : Nat) :
    edgeSource 0 136 code = 311040+code/6 := by rfl

theorem target_136_0 (code : Nat) :
    edgeTarget 0 136 code = 738720+code%7776 := by rfl

theorem block_136_0 :
    savedBlockClass (75*136+0) = some 64 ∧
    recordedClassRoot 64 = 3479 := by decide +kernel

theorem completed_136_0 (code : Nat) :
    weight completedCredit 0 136 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 136 [] 13 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_136_0 direction_136.1
    direction_136.2.1 conditioned_136 code

theorem conditional_136_0 (code : Nat) :
    weight conditionalCredit 0 136 code =
      120*(code%6+1)+max (max 13 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 136 [] 13 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_136_0 direction_136.1
    direction_136.2.2 conditioned_136 code
#print axioms selected_136_0
#print axioms source_136_0
#print axioms target_136_0
#print axioms block_136_0
#print axioms completed_136_0
#print axioms conditional_136_0

theorem selected_137_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [137])) := by rfl

theorem source_137_0 (code : Nat) :
    edgeSource 0 137 code = 318816+code/6 := by rfl

theorem target_137_0 (code : Nat) :
    edgeTarget 0 137 code = 754272+code%7776 := by rfl

theorem block_137_0 :
    savedBlockClass (75*137+0) = some 68 ∧
    recordedClassRoot 68 = 3493 := by decide +kernel

theorem completed_137_0 (code : Nat) :
    weight completedCredit 0 137 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 137 [] 14 16
    (fun code => 0) selected_137_0 direction_137.1
    direction_137.2.1 conditioned_137 code

theorem conditional_137_0 (code : Nat) :
    weight conditionalCredit 0 137 code =
      120*(code%6+1)+max (max 14 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 137 [] 14 16
    (fun code => 0) selected_137_0 direction_137.1
    direction_137.2.2 conditioned_137 code
#print axioms selected_137_0
#print axioms source_137_0
#print axioms target_137_0
#print axioms block_137_0
#print axioms completed_137_0
#print axioms conditional_137_0

theorem selected_138_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [138])) := by rfl

theorem source_138_0 (code : Nat) :
    edgeSource 0 138 code = 318816+code/6 := by rfl

theorem target_138_0 (code : Nat) :
    edgeTarget 0 138 code = 769824+code%7776 := by rfl

theorem block_138_0 :
    savedBlockClass (75*138+0) = some 69 ∧
    recordedClassRoot 69 = 3497 := by decide +kernel

theorem completed_138_0 (code : Nat) :
    weight completedCredit 0 138 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 138 [] 18 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_138_0 direction_138.1
    direction_138.2.1 conditioned_138 code

theorem conditional_138_0 (code : Nat) :
    weight conditionalCredit 0 138 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 138 [] 18 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_138_0 direction_138.1
    direction_138.2.2 conditioned_138 code
#print axioms selected_138_0
#print axioms source_138_0
#print axioms target_138_0
#print axioms block_138_0
#print axioms completed_138_0
#print axioms conditional_138_0

theorem selected_139_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [139])) := by rfl

theorem source_139_0 (code : Nat) :
    edgeSource 0 139 code = 326592+code/6 := by rfl

theorem target_139_0 (code : Nat) :
    edgeTarget 0 139 code = 1088640+code%7776 := by rfl

theorem block_139_0 :
    savedBlockClass (75*139+0) = some 70 ∧
    recordedClassRoot 70 = 3500 := by decide +kernel

theorem completed_139_0 (code : Nat) :
    weight completedCredit 0 139 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 139 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_139_0 direction_139.1
    direction_139.2.1 conditioned_139 code

theorem conditional_139_0 (code : Nat) :
    weight conditionalCredit 0 139 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 139 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_139_0 direction_139.1
    direction_139.2.2 conditioned_139 code
#print axioms selected_139_0
#print axioms source_139_0
#print axioms target_139_0
#print axioms block_139_0
#print axioms completed_139_0
#print axioms conditional_139_0

theorem selected_139_7 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 7 [] ++ [139])) := by rfl

theorem source_139_7 (code : Nat) :
    edgeSource 7 139 code = 1073088+code/6 := by rfl

theorem target_139_7 (code : Nat) :
    edgeTarget 7 139 code = 1329696+code%7776 := by rfl

theorem block_139_7 :
    savedBlockClass (75*139+7) = some 70 ∧
    recordedClassRoot 70 = 3500 := by decide +kernel

theorem completed_139_7 (code : Nat) :
    weight completedCredit 7 139 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 7 139 [] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_139_7 direction_139.1
    direction_139.2.1 conditioned_139 code

theorem conditional_139_7 (code : Nat) :
    weight conditionalCredit 7 139 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 7 139 [] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_139_7 direction_139.1
    direction_139.2.2 conditioned_139 code
#print axioms selected_139_7
#print axioms source_139_7
#print axioms target_139_7
#print axioms block_139_7
#print axioms completed_139_7
#print axioms conditional_139_7

theorem selected_139_56 :
    [rule033] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 56 [] ++ [139])) := by rfl

theorem source_139_56 (code : Nat) :
    edgeSource 56 139 code = 1454112+code/6 := by rfl

theorem target_139_56 (code : Nat) :
    edgeTarget 56 139 code = 1329696+code%7776 := by rfl

theorem block_139_56 :
    savedBlockClass (75*139+56) = some 70 ∧
    recordedClassRoot 70 = 3500 := by decide +kernel

theorem completed_139_56 (code : Nat) :
    weight completedCredit 56 139 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule033] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 56 139 [rule033] 0 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_139_56 direction_139.1
    direction_139.2.1 conditioned_139 code

theorem conditional_139_56 (code : Nat) :
    weight conditionalCredit 56 139 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule033] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 56 139 [rule033] 0 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_139_56 direction_139.1
    direction_139.2.2 conditioned_139 code
#print axioms selected_139_56
#print axioms source_139_56
#print axioms target_139_56
#print axioms block_139_56
#print axioms completed_139_56
#print axioms conditional_139_56

theorem selected_140_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [140])) := by rfl

theorem source_140_0 (code : Nat) :
    edgeSource 0 140 code = 334368+code/6 := by rfl

theorem target_140_0 (code : Nat) :
    edgeTarget 0 140 code = 808704+code%7776 := by rfl

theorem block_140_0 :
    savedBlockClass (75*140+0) = some 68 ∧
    recordedClassRoot 68 = 3493 := by decide +kernel

theorem completed_140_0 (code : Nat) :
    weight completedCredit 0 140 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 140 [] 10 16
    (fun code => 0) selected_140_0 direction_140.1
    direction_140.2.1 conditioned_140 code

theorem conditional_140_0 (code : Nat) :
    weight conditionalCredit 0 140 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 140 [] 10 16
    (fun code => 0) selected_140_0 direction_140.1
    direction_140.2.2 conditioned_140 code
#print axioms selected_140_0
#print axioms source_140_0
#print axioms target_140_0
#print axioms block_140_0
#print axioms completed_140_0
#print axioms conditional_140_0

theorem selected_141_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [141])) := by rfl

theorem source_141_0 (code : Nat) :
    edgeSource 0 141 code = 334368+code/6 := by rfl

theorem target_141_0 (code : Nat) :
    edgeTarget 0 141 code = 793152+code%7776 := by rfl

theorem block_141_0 :
    savedBlockClass (75*141+0) = some 69 ∧
    recordedClassRoot 69 = 3497 := by decide +kernel

theorem completed_141_0 (code : Nat) :
    weight completedCredit 0 141 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 141 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_141_0 direction_141.1
    direction_141.2.1 conditioned_141 code

theorem conditional_141_0 (code : Nat) :
    weight conditionalCredit 0 141 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 141 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_141_0 direction_141.1
    direction_141.2.2 conditioned_141 code
#print axioms selected_141_0
#print axioms source_141_0
#print axioms target_141_0
#print axioms block_141_0
#print axioms completed_141_0
#print axioms conditional_141_0

theorem selected_142_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [142])) := by rfl

theorem source_142_0 (code : Nat) :
    edgeSource 0 142 code = 334368+code/6 := by rfl

theorem target_142_0 (code : Nat) :
    edgeTarget 0 142 code = 800928+code%7776 := by rfl

theorem block_142_0 :
    savedBlockClass (75*142+0) = some 69 ∧
    recordedClassRoot 69 = 3497 := by decide +kernel

theorem completed_142_0 (code : Nat) :
    weight completedCredit 0 142 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 142 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_142_0 direction_142.1
    direction_142.2.1 conditioned_142 code

theorem conditional_142_0 (code : Nat) :
    weight conditionalCredit 0 142 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 142 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_142_0 direction_142.1
    direction_142.2.2 conditioned_142 code
#print axioms selected_142_0
#print axioms source_142_0
#print axioms target_142_0
#print axioms block_142_0
#print axioms completed_142_0
#print axioms conditional_142_0

theorem selected_143_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [143])) := by rfl

theorem source_143_0 (code : Nat) :
    edgeSource 0 143 code = 334368+code/6 := by rfl

theorem target_143_0 (code : Nat) :
    edgeTarget 0 143 code = 816480+code%7776 := by rfl

theorem block_143_0 :
    savedBlockClass (75*143+0) = some 71 ∧
    recordedClassRoot 71 = 3504 := by decide +kernel

theorem completed_143_0 (code : Nat) :
    weight completedCredit 0 143 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 143 [] 5 0
    (fun code => 0) selected_143_0 direction_143.1
    direction_143.2.1 conditioned_143 code

theorem conditional_143_0 (code : Nat) :
    weight conditionalCredit 0 143 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 143 [] 5 16
    (fun code => 0) selected_143_0 direction_143.1
    direction_143.2.2 conditioned_143 code
#print axioms selected_143_0
#print axioms source_143_0
#print axioms target_143_0
#print axioms block_143_0
#print axioms completed_143_0
#print axioms conditional_143_0

theorem selected_144_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [144])) := by rfl

theorem source_144_0 (code : Nat) :
    edgeSource 0 144 code = 334368+code/6 := by rfl

theorem target_144_0 (code : Nat) :
    edgeTarget 0 144 code = 824256+code%7776 := by rfl

theorem block_144_0 :
    savedBlockClass (75*144+0) = some 69 ∧
    recordedClassRoot 69 = 3497 := by decide +kernel

theorem completed_144_0 (code : Nat) :
    weight completedCredit 0 144 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 144 [] 10 0
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_144_0 direction_144.1
    direction_144.2.1 conditioned_144 code

theorem conditional_144_0 (code : Nat) :
    weight conditionalCredit 0 144 code =
      120*(code%6+1)+max (max 10 (emittedCredit [] code))
        (max ((if code%7776 = 7106 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 144 [] 10 18
    (fun code => (if code%7776 = 7106 then 96 else 0)) selected_144_0 direction_144.1
    direction_144.2.2 conditioned_144 code
#print axioms selected_144_0
#print axioms source_144_0
#print axioms target_144_0
#print axioms block_144_0
#print axioms completed_144_0
#print axioms conditional_144_0

theorem selected_145_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [145])) := by rfl

theorem source_145_0 (code : Nat) :
    edgeSource 0 145 code = 342144+code/6 := by rfl

theorem target_145_0 (code : Nat) :
    edgeTarget 0 145 code = 948672+code%7776 := by rfl

theorem block_145_0 :
    savedBlockClass (75*145+0) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_145_0 (code : Nat) :
    weight completedCredit 0 145 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 145 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_145_0 direction_145.1
    direction_145.2.1 conditioned_145 code

theorem conditional_145_0 (code : Nat) :
    weight conditionalCredit 0 145 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 145 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_145_0 direction_145.1
    direction_145.2.2 conditioned_145 code
#print axioms selected_145_0
#print axioms source_145_0
#print axioms target_145_0
#print axioms block_145_0
#print axioms completed_145_0
#print axioms conditional_145_0

theorem selected_145_8 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 8 [] ++ [145])) := by rfl

theorem source_145_8 (code : Nat) :
    edgeSource 8 145 code = 1080864+code/6 := by rfl

theorem target_145_8 (code : Nat) :
    edgeTarget 8 145 code = 948672+code%7776 := by rfl

theorem block_145_8 :
    savedBlockClass (75*145+8) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_145_8 (code : Nat) :
    weight completedCredit 8 145 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 8 145 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_145_8 direction_145.1
    direction_145.2.1 conditioned_145 code

theorem conditional_145_8 (code : Nat) :
    weight conditionalCredit 8 145 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 8 145 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_145_8 direction_145.1
    direction_145.2.2 conditioned_145 code
#print axioms selected_145_8
#print axioms source_145_8
#print axioms target_145_8
#print axioms block_145_8
#print axioms completed_145_8
#print axioms conditional_145_8

theorem selected_145_57 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 57 [] ++ [145])) := by rfl

theorem source_145_57 (code : Nat) :
    edgeSource 57 145 code = 1461888+code/6 := by rfl

theorem target_145_57 (code : Nat) :
    edgeTarget 57 145 code = 948672+code%7776 := by rfl

theorem block_145_57 :
    savedBlockClass (75*145+57) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_145_57 (code : Nat) :
    weight completedCredit 57 145 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 57 145 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_145_57 direction_145.1
    direction_145.2.1 conditioned_145 code

theorem conditional_145_57 (code : Nat) :
    weight conditionalCredit 57 145 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 57 145 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_145_57 direction_145.1
    direction_145.2.2 conditioned_145 code
#print axioms selected_145_57
#print axioms source_145_57
#print axioms target_145_57
#print axioms block_145_57
#print axioms completed_145_57
#print axioms conditional_145_57

theorem selected_146_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [146])) := by rfl

theorem source_146_0 (code : Nat) :
    edgeSource 0 146 code = 342144+code/6 := by rfl

theorem target_146_0 (code : Nat) :
    edgeTarget 0 146 code = 956448+code%7776 := by rfl

theorem block_146_0 :
    savedBlockClass (75*146+0) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_146_0 (code : Nat) :
    weight completedCredit 0 146 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 146 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_146_0 direction_146.1
    direction_146.2.1 conditioned_146 code

theorem conditional_146_0 (code : Nat) :
    weight conditionalCredit 0 146 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 146 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_146_0 direction_146.1
    direction_146.2.2 conditioned_146 code
#print axioms selected_146_0
#print axioms source_146_0
#print axioms target_146_0
#print axioms block_146_0
#print axioms completed_146_0
#print axioms conditional_146_0

theorem selected_146_8 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 8 [] ++ [146])) := by rfl

theorem source_146_8 (code : Nat) :
    edgeSource 8 146 code = 1080864+code/6 := by rfl

theorem target_146_8 (code : Nat) :
    edgeTarget 8 146 code = 956448+code%7776 := by rfl

theorem block_146_8 :
    savedBlockClass (75*146+8) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_146_8 (code : Nat) :
    weight completedCredit 8 146 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 8 146 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_146_8 direction_146.1
    direction_146.2.1 conditioned_146 code

theorem conditional_146_8 (code : Nat) :
    weight conditionalCredit 8 146 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 8 146 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_146_8 direction_146.1
    direction_146.2.2 conditioned_146 code
#print axioms selected_146_8
#print axioms source_146_8
#print axioms target_146_8
#print axioms block_146_8
#print axioms completed_146_8
#print axioms conditional_146_8

theorem selected_146_57 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 57 [] ++ [146])) := by rfl

theorem source_146_57 (code : Nat) :
    edgeSource 57 146 code = 1461888+code/6 := by rfl

theorem target_146_57 (code : Nat) :
    edgeTarget 57 146 code = 956448+code%7776 := by rfl

theorem block_146_57 :
    savedBlockClass (75*146+57) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_146_57 (code : Nat) :
    weight completedCredit 57 146 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 57 146 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_146_57 direction_146.1
    direction_146.2.1 conditioned_146 code

theorem conditional_146_57 (code : Nat) :
    weight conditionalCredit 57 146 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 57 146 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_146_57 direction_146.1
    direction_146.2.2 conditioned_146 code
#print axioms selected_146_57
#print axioms source_146_57
#print axioms target_146_57
#print axioms block_146_57
#print axioms completed_146_57
#print axioms conditional_146_57

theorem selected_147_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [147])) := by rfl

theorem source_147_0 (code : Nat) :
    edgeSource 0 147 code = 342144+code/6 := by rfl

theorem target_147_0 (code : Nat) :
    edgeTarget 0 147 code = 1096416+code%7776 := by rfl

theorem block_147_0 :
    savedBlockClass (75*147+0) = some 73 ∧
    recordedClassRoot 73 = 3511 := by decide +kernel

theorem completed_147_0 (code : Nat) :
    weight completedCredit 0 147 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 147 [] 0 12
    (fun code => 0) selected_147_0 direction_147.1
    direction_147.2.1 conditioned_147 code

theorem conditional_147_0 (code : Nat) :
    weight conditionalCredit 0 147 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 147 [] 0 12
    (fun code => 0) selected_147_0 direction_147.1
    direction_147.2.2 conditioned_147 code
#print axioms selected_147_0
#print axioms source_147_0
#print axioms target_147_0
#print axioms block_147_0
#print axioms completed_147_0
#print axioms conditional_147_0

theorem selected_147_8 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 8 [] ++ [147])) := by rfl

theorem source_147_8 (code : Nat) :
    edgeSource 8 147 code = 1080864+code/6 := by rfl

theorem target_147_8 (code : Nat) :
    edgeTarget 8 147 code = 1337472+code%7776 := by rfl

theorem block_147_8 :
    savedBlockClass (75*147+8) = some 73 ∧
    recordedClassRoot 73 = 3511 := by decide +kernel

theorem completed_147_8 (code : Nat) :
    weight completedCredit 8 147 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 8 147 [] 0 12
    (fun code => 0) selected_147_8 direction_147.1
    direction_147.2.1 conditioned_147 code

theorem conditional_147_8 (code : Nat) :
    weight conditionalCredit 8 147 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 8 147 [] 0 12
    (fun code => 0) selected_147_8 direction_147.1
    direction_147.2.2 conditioned_147 code
#print axioms selected_147_8
#print axioms source_147_8
#print axioms target_147_8
#print axioms block_147_8
#print axioms completed_147_8
#print axioms conditional_147_8

theorem selected_147_57 :
    [rule034] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 57 [] ++ [147])) := by rfl

theorem source_147_57 (code : Nat) :
    edgeSource 57 147 code = 1461888+code/6 := by rfl

theorem target_147_57 (code : Nat) :
    edgeTarget 57 147 code = 1337472+code%7776 := by rfl

theorem block_147_57 :
    savedBlockClass (75*147+57) = some 73 ∧
    recordedClassRoot 73 = 3511 := by decide +kernel

theorem completed_147_57 (code : Nat) :
    weight completedCredit 57 147 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule034] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 57 147 [rule034] 0 12
    (fun code => 0) selected_147_57 direction_147.1
    direction_147.2.1 conditioned_147 code

theorem conditional_147_57 (code : Nat) :
    weight conditionalCredit 57 147 code =
      120*(code%6+1)+max (max 0 (emittedCredit [rule034] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 57 147 [rule034] 0 12
    (fun code => 0) selected_147_57 direction_147.1
    direction_147.2.2 conditioned_147 code
#print axioms selected_147_57
#print axioms source_147_57
#print axioms target_147_57
#print axioms block_147_57
#print axioms completed_147_57
#print axioms conditional_147_57

theorem selected_148_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [148])) := by rfl

theorem source_148_0 (code : Nat) :
    edgeSource 0 148 code = 342144+code/6 := by rfl

theorem target_148_0 (code : Nat) :
    edgeTarget 0 148 code = 972000+code%7776 := by rfl

theorem block_148_0 :
    savedBlockClass (75*148+0) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_148_0 (code : Nat) :
    weight completedCredit 0 148 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 148 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_148_0 direction_148.1
    direction_148.2.1 conditioned_148 code

theorem conditional_148_0 (code : Nat) :
    weight conditionalCredit 0 148 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 148 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_148_0 direction_148.1
    direction_148.2.2 conditioned_148 code
#print axioms selected_148_0
#print axioms source_148_0
#print axioms target_148_0
#print axioms block_148_0
#print axioms completed_148_0
#print axioms conditional_148_0

theorem selected_148_8 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 8 [] ++ [148])) := by rfl

theorem source_148_8 (code : Nat) :
    edgeSource 8 148 code = 1080864+code/6 := by rfl

theorem target_148_8 (code : Nat) :
    edgeTarget 8 148 code = 972000+code%7776 := by rfl

theorem block_148_8 :
    savedBlockClass (75*148+8) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_148_8 (code : Nat) :
    weight completedCredit 8 148 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 8 148 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_148_8 direction_148.1
    direction_148.2.1 conditioned_148 code

theorem conditional_148_8 (code : Nat) :
    weight conditionalCredit 8 148 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 8 148 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_148_8 direction_148.1
    direction_148.2.2 conditioned_148 code
#print axioms selected_148_8
#print axioms source_148_8
#print axioms target_148_8
#print axioms block_148_8
#print axioms completed_148_8
#print axioms conditional_148_8

theorem selected_148_57 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 57 [] ++ [148])) := by rfl

theorem source_148_57 (code : Nat) :
    edgeSource 57 148 code = 1461888+code/6 := by rfl

theorem target_148_57 (code : Nat) :
    edgeTarget 57 148 code = 972000+code%7776 := by rfl

theorem block_148_57 :
    savedBlockClass (75*148+57) = some 72 ∧
    recordedClassRoot 72 = 3508 := by decide +kernel

theorem completed_148_57 (code : Nat) :
    weight completedCredit 57 148 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 57 148 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_148_57 direction_148.1
    direction_148.2.1 conditioned_148 code

theorem conditional_148_57 (code : Nat) :
    weight conditionalCredit 57 148 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 57 148 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_148_57 direction_148.1
    direction_148.2.2 conditioned_148 code
#print axioms selected_148_57
#print axioms source_148_57
#print axioms target_148_57
#print axioms block_148_57
#print axioms completed_148_57
#print axioms conditional_148_57

theorem selected_149_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [149])) := by rfl

theorem source_149_0 (code : Nat) :
    edgeSource 0 149 code = 349920+code/6 := by rfl

theorem target_149_0 (code : Nat) :
    edgeTarget 0 149 code = 847584+code%7776 := by rfl

theorem block_149_0 :
    savedBlockClass (75*149+0) = some 58 ∧
    recordedClassRoot 58 = 3459 := by decide +kernel

theorem completed_149_0 (code : Nat) :
    weight completedCredit 0 149 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 149 [] 0 16
    (fun code => 0) selected_149_0 direction_149.1
    direction_149.2.1 conditioned_149 code

theorem conditional_149_0 (code : Nat) :
    weight conditionalCredit 0 149 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 149 [] 0 16
    (fun code => 0) selected_149_0 direction_149.1
    direction_149.2.2 conditioned_149 code
#print axioms selected_149_0
#print axioms source_149_0
#print axioms target_149_0
#print axioms block_149_0
#print axioms completed_149_0
#print axioms conditional_149_0

theorem selected_150_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [150])) := by rfl

theorem source_150_0 (code : Nat) :
    edgeSource 0 150 code = 349920+code/6 := by rfl

theorem target_150_0 (code : Nat) :
    edgeTarget 0 150 code = 832032+code%7776 := by rfl

theorem block_150_0 :
    savedBlockClass (75*150+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_150_0 (code : Nat) :
    weight completedCredit 0 150 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 150 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_150_0 direction_150.1
    direction_150.2.1 conditioned_150 code

theorem conditional_150_0 (code : Nat) :
    weight conditionalCredit 0 150 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 150 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_150_0 direction_150.1
    direction_150.2.2 conditioned_150 code
#print axioms selected_150_0
#print axioms source_150_0
#print axioms target_150_0
#print axioms block_150_0
#print axioms completed_150_0
#print axioms conditional_150_0

theorem selected_151_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [151])) := by rfl

theorem source_151_0 (code : Nat) :
    edgeSource 0 151 code = 349920+code/6 := by rfl

theorem target_151_0 (code : Nat) :
    edgeTarget 0 151 code = 839808+code%7776 := by rfl

theorem block_151_0 :
    savedBlockClass (75*151+0) = some 60 ∧
    recordedClassRoot 60 = 3465 := by decide +kernel

theorem completed_151_0 (code : Nat) :
    weight completedCredit 0 151 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 151 [] 0 0
    (fun code => 0) selected_151_0 direction_151.1
    direction_151.2.1 conditioned_151 code

theorem conditional_151_0 (code : Nat) :
    weight conditionalCredit 0 151 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 151 [] 0 16
    (fun code => 0) selected_151_0 direction_151.1
    direction_151.2.2 conditioned_151 code
#print axioms selected_151_0
#print axioms source_151_0
#print axioms target_151_0
#print axioms block_151_0
#print axioms completed_151_0
#print axioms conditional_151_0

theorem selected_152_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [152])) := by rfl

theorem source_152_0 (code : Nat) :
    edgeSource 0 152 code = 349920+code/6 := by rfl

theorem target_152_0 (code : Nat) :
    edgeTarget 0 152 code = 855360+code%7776 := by rfl

theorem block_152_0 :
    savedBlockClass (75*152+0) = some 61 ∧
    recordedClassRoot 61 = 3469 := by decide +kernel

theorem completed_152_0 (code : Nat) :
    weight completedCredit 0 152 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 152 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_152_0 direction_152.1
    direction_152.2.1 conditioned_152 code

theorem conditional_152_0 (code : Nat) :
    weight conditionalCredit 0 152 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 152 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_152_0 direction_152.1
    direction_152.2.2 conditioned_152 code
#print axioms selected_152_0
#print axioms source_152_0
#print axioms target_152_0
#print axioms block_152_0
#print axioms completed_152_0
#print axioms conditional_152_0

theorem selected_153_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [153])) := by rfl

theorem source_153_0 (code : Nat) :
    edgeSource 0 153 code = 349920+code/6 := by rfl

theorem target_153_0 (code : Nat) :
    edgeTarget 0 153 code = 863136+code%7776 := by rfl

theorem block_153_0 :
    savedBlockClass (75*153+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_153_0 (code : Nat) :
    weight completedCredit 0 153 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 153 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_153_0 direction_153.1
    direction_153.2.1 conditioned_153 code

theorem conditional_153_0 (code : Nat) :
    weight conditionalCredit 0 153 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 153 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_153_0 direction_153.1
    direction_153.2.2 conditioned_153 code
#print axioms selected_153_0
#print axioms source_153_0
#print axioms target_153_0
#print axioms block_153_0
#print axioms completed_153_0
#print axioms conditional_153_0

theorem selected_154_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [154])) := by rfl

theorem source_154_0 (code : Nat) :
    edgeSource 0 154 code = 357696+code/6 := by rfl

theorem target_154_0 (code : Nat) :
    edgeTarget 0 154 code = 886464+code%7776 := by rfl

theorem block_154_0 :
    savedBlockClass (75*154+0) = some 54 ∧
    recordedClassRoot 54 = 3447 := by decide +kernel

theorem completed_154_0 (code : Nat) :
    weight completedCredit 0 154 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 154 [] 0 16
    (fun code => 0) selected_154_0 direction_154.1
    direction_154.2.1 conditioned_154 code

theorem conditional_154_0 (code : Nat) :
    weight conditionalCredit 0 154 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 154 [] 0 16
    (fun code => 0) selected_154_0 direction_154.1
    direction_154.2.2 conditioned_154 code
#print axioms selected_154_0
#print axioms source_154_0
#print axioms target_154_0
#print axioms block_154_0
#print axioms completed_154_0
#print axioms conditional_154_0

theorem selected_155_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [155])) := by rfl

theorem source_155_0 (code : Nat) :
    edgeSource 0 155 code = 357696+code/6 := by rfl

theorem target_155_0 (code : Nat) :
    edgeTarget 0 155 code = 870912+code%7776 := by rfl

theorem block_155_0 :
    savedBlockClass (75*155+0) = some 55 ∧
    recordedClassRoot 55 = 3450 := by decide +kernel

theorem completed_155_0 (code : Nat) :
    weight completedCredit 0 155 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 155 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_155_0 direction_155.1
    direction_155.2.1 conditioned_155 code

theorem conditional_155_0 (code : Nat) :
    weight conditionalCredit 0 155 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 155 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_155_0 direction_155.1
    direction_155.2.2 conditioned_155 code
#print axioms selected_155_0
#print axioms source_155_0
#print axioms target_155_0
#print axioms block_155_0
#print axioms completed_155_0
#print axioms conditional_155_0

theorem selected_156_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [156])) := by rfl

theorem source_156_0 (code : Nat) :
    edgeSource 0 156 code = 357696+code/6 := by rfl

theorem target_156_0 (code : Nat) :
    edgeTarget 0 156 code = 878688+code%7776 := by rfl

theorem block_156_0 :
    savedBlockClass (75*156+0) = some 74 ∧
    recordedClassRoot 74 = 3514 := by decide +kernel

theorem completed_156_0 (code : Nat) :
    weight completedCredit 0 156 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 156 [] 0 0
    (fun code => 0) selected_156_0 direction_156.1
    direction_156.2.1 conditioned_156 code

theorem conditional_156_0 (code : Nat) :
    weight conditionalCredit 0 156 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 156 [] 0 16
    (fun code => 0) selected_156_0 direction_156.1
    direction_156.2.2 conditioned_156 code
#print axioms selected_156_0
#print axioms source_156_0
#print axioms target_156_0
#print axioms block_156_0
#print axioms completed_156_0
#print axioms conditional_156_0

theorem selected_157_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [157])) := by rfl

theorem source_157_0 (code : Nat) :
    edgeSource 0 157 code = 357696+code/6 := by rfl

theorem target_157_0 (code : Nat) :
    edgeTarget 0 157 code = 894240+code%7776 := by rfl

theorem block_157_0 :
    savedBlockClass (75*157+0) = some 75 ∧
    recordedClassRoot 75 = 3517 := by decide +kernel

theorem completed_157_0 (code : Nat) :
    weight completedCredit 0 157 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 157 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_157_0 direction_157.1
    direction_157.2.1 conditioned_157 code

theorem conditional_157_0 (code : Nat) :
    weight conditionalCredit 0 157 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 157 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_157_0 direction_157.1
    direction_157.2.2 conditioned_157 code
#print axioms selected_157_0
#print axioms source_157_0
#print axioms target_157_0
#print axioms block_157_0
#print axioms completed_157_0
#print axioms conditional_157_0

theorem selected_158_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [158])) := by rfl

theorem source_158_0 (code : Nat) :
    edgeSource 0 158 code = 357696+code/6 := by rfl

theorem target_158_0 (code : Nat) :
    edgeTarget 0 158 code = 902016+code%7776 := by rfl

theorem block_158_0 :
    savedBlockClass (75*158+0) = some 55 ∧
    recordedClassRoot 55 = 3450 := by decide +kernel

theorem completed_158_0 (code : Nat) :
    weight completedCredit 0 158 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 158 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_158_0 direction_158.1
    direction_158.2.1 conditioned_158 code

theorem conditional_158_0 (code : Nat) :
    weight conditionalCredit 0 158 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 158 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_158_0 direction_158.1
    direction_158.2.2 conditioned_158 code
#print axioms selected_158_0
#print axioms source_158_0
#print axioms target_158_0
#print axioms block_158_0
#print axioms completed_158_0
#print axioms conditional_158_0

theorem selected_159_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [159])) := by rfl

theorem source_159_0 (code : Nat) :
    edgeSource 0 159 code = 365472+code/6 := by rfl

theorem target_159_0 (code : Nat) :
    edgeTarget 0 159 code = 925344+code%7776 := by rfl

theorem block_159_0 :
    savedBlockClass (75*159+0) = some 76 ∧
    recordedClassRoot 76 = 3519 := by decide +kernel

theorem completed_159_0 (code : Nat) :
    weight completedCredit 0 159 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 159 [] 6 0
    (fun code => 0) selected_159_0 direction_159.1
    direction_159.2.1 conditioned_159 code

theorem conditional_159_0 (code : Nat) :
    weight conditionalCredit 0 159 code =
      120*(code%6+1)+max (max 6 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 159 [] 6 16
    (fun code => 0) selected_159_0 direction_159.1
    direction_159.2.2 conditioned_159 code
#print axioms selected_159_0
#print axioms source_159_0
#print axioms target_159_0
#print axioms block_159_0
#print axioms completed_159_0
#print axioms conditional_159_0

theorem selected_160_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [160])) := by rfl

theorem source_160_0 (code : Nat) :
    edgeSource 0 160 code = 365472+code/6 := by rfl

theorem target_160_0 (code : Nat) :
    edgeTarget 0 160 code = 909792+code%7776 := by rfl

theorem block_160_0 :
    savedBlockClass (75*160+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_160_0 (code : Nat) :
    weight completedCredit 0 160 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 160 [] 18 16
    (fun code => 0) selected_160_0 direction_160.1
    direction_160.2.1 conditioned_160 code

theorem conditional_160_0 (code : Nat) :
    weight conditionalCredit 0 160 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 160 [] 18 16
    (fun code => 0) selected_160_0 direction_160.1
    direction_160.2.2 conditioned_160 code
#print axioms selected_160_0
#print axioms source_160_0
#print axioms target_160_0
#print axioms block_160_0
#print axioms completed_160_0
#print axioms conditional_160_0

theorem selected_161_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [161])) := by rfl

theorem source_161_0 (code : Nat) :
    edgeSource 0 161 code = 365472+code/6 := by rfl

theorem target_161_0 (code : Nat) :
    edgeTarget 0 161 code = 917568+code%7776 := by rfl

theorem block_161_0 :
    savedBlockClass (75*161+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_161_0 (code : Nat) :
    weight completedCredit 0 161 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 161 [] 18 16
    (fun code => 0) selected_161_0 direction_161.1
    direction_161.2.1 conditioned_161 code

theorem conditional_161_0 (code : Nat) :
    weight conditionalCredit 0 161 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 161 [] 18 16
    (fun code => 0) selected_161_0 direction_161.1
    direction_161.2.2 conditioned_161 code
#print axioms selected_161_0
#print axioms source_161_0
#print axioms target_161_0
#print axioms block_161_0
#print axioms completed_161_0
#print axioms conditional_161_0

theorem selected_162_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [162])) := by rfl

theorem source_162_0 (code : Nat) :
    edgeSource 0 162 code = 365472+code/6 := by rfl

theorem target_162_0 (code : Nat) :
    edgeTarget 0 162 code = 933120+code%7776 := by rfl

theorem block_162_0 :
    savedBlockClass (75*162+0) = some 77 ∧
    recordedClassRoot 77 = 3522 := by decide +kernel

theorem completed_162_0 (code : Nat) :
    weight completedCredit 0 162 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 162 [] 12 16
    (fun code => 0) selected_162_0 direction_162.1
    direction_162.2.1 conditioned_162 code

theorem conditional_162_0 (code : Nat) :
    weight conditionalCredit 0 162 code =
      120*(code%6+1)+max (max 12 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 162 [] 12 16
    (fun code => 0) selected_162_0 direction_162.1
    direction_162.2.2 conditioned_162 code
#print axioms selected_162_0
#print axioms source_162_0
#print axioms target_162_0
#print axioms block_162_0
#print axioms completed_162_0
#print axioms conditional_162_0

theorem selected_163_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [163])) := by rfl

theorem source_163_0 (code : Nat) :
    edgeSource 0 163 code = 365472+code/6 := by rfl

theorem target_163_0 (code : Nat) :
    edgeTarget 0 163 code = 940896+code%7776 := by rfl

theorem block_163_0 :
    savedBlockClass (75*163+0) = some 57 ∧
    recordedClassRoot 57 = 3456 := by decide +kernel

theorem completed_163_0 (code : Nat) :
    weight completedCredit 0 163 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 163 [] 18 16
    (fun code => 0) selected_163_0 direction_163.1
    direction_163.2.1 conditioned_163 code

theorem conditional_163_0 (code : Nat) :
    weight conditionalCredit 0 163 code =
      120*(code%6+1)+max (max 18 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 163 [] 18 16
    (fun code => 0) selected_163_0 direction_163.1
    direction_163.2.2 conditioned_163 code
#print axioms selected_163_0
#print axioms source_163_0
#print axioms target_163_0
#print axioms block_163_0
#print axioms completed_163_0
#print axioms conditional_163_0

theorem selected_164_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [164])) := by rfl

theorem source_164_0 (code : Nat) :
    edgeSource 0 164 code = 373248+code/6 := by rfl

theorem target_164_0 (code : Nat) :
    edgeTarget 0 164 code = 1003104+code%7776 := by rfl

theorem block_164_0 :
    savedBlockClass (75*164+0) = some 58 ∧
    recordedClassRoot 58 = 3459 := by decide +kernel

theorem completed_164_0 (code : Nat) :
    weight completedCredit 0 164 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context completedCredit 0 164 [] 0 16
    (fun code => 0) selected_164_0 direction_164.1
    direction_164.2.1 conditioned_164 code

theorem conditional_164_0 (code : Nat) :
    weight conditionalCredit 0 164 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 164 [] 0 16
    (fun code => 0) selected_164_0 direction_164.1
    direction_164.2.2 conditioned_164 code
#print axioms selected_164_0
#print axioms source_164_0
#print axioms target_164_0
#print axioms block_164_0
#print axioms completed_164_0
#print axioms conditional_164_0

theorem selected_165_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [165])) := by rfl

theorem source_165_0 (code : Nat) :
    edgeSource 0 165 code = 373248+code/6 := by rfl

theorem target_165_0 (code : Nat) :
    edgeTarget 0 165 code = 979776+code%7776 := by rfl

theorem block_165_0 :
    savedBlockClass (75*165+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_165_0 (code : Nat) :
    weight completedCredit 0 165 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 165 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_165_0 direction_165.1
    direction_165.2.1 conditioned_165 code

theorem conditional_165_0 (code : Nat) :
    weight conditionalCredit 0 165 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 165 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_165_0 direction_165.1
    direction_165.2.2 conditioned_165 code
#print axioms selected_165_0
#print axioms source_165_0
#print axioms target_165_0
#print axioms block_165_0
#print axioms completed_165_0
#print axioms conditional_165_0

theorem selected_166_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [166])) := by rfl

theorem source_166_0 (code : Nat) :
    edgeSource 0 166 code = 373248+code/6 := by rfl

theorem target_166_0 (code : Nat) :
    edgeTarget 0 166 code = 987552+code%7776 := by rfl

theorem block_166_0 :
    savedBlockClass (75*166+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_166_0 (code : Nat) :
    weight completedCredit 0 166 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 166 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_166_0 direction_166.1
    direction_166.2.1 conditioned_166 code

theorem conditional_166_0 (code : Nat) :
    weight conditionalCredit 0 166 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 166 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_166_0 direction_166.1
    direction_166.2.2 conditioned_166 code
#print axioms selected_166_0
#print axioms source_166_0
#print axioms target_166_0
#print axioms block_166_0
#print axioms completed_166_0
#print axioms conditional_166_0

theorem selected_167_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [167])) := by rfl

theorem source_167_0 (code : Nat) :
    edgeSource 0 167 code = 373248+code/6 := by rfl

theorem target_167_0 (code : Nat) :
    edgeTarget 0 167 code = 995328+code%7776 := by rfl

theorem block_167_0 :
    savedBlockClass (75*167+0) = some 60 ∧
    recordedClassRoot 60 = 3465 := by decide +kernel

theorem completed_167_0 (code : Nat) :
    weight completedCredit 0 167 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 0) :=
  weight_eq_context completedCredit 0 167 [] 0 0
    (fun code => 0) selected_167_0 direction_167.1
    direction_167.2.1 conditioned_167 code

theorem conditional_167_0 (code : Nat) :
    weight conditionalCredit 0 167 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 16) :=
  weight_eq_context conditionalCredit 0 167 [] 0 16
    (fun code => 0) selected_167_0 direction_167.1
    direction_167.2.2 conditioned_167 code
#print axioms selected_167_0
#print axioms source_167_0
#print axioms target_167_0
#print axioms block_167_0
#print axioms completed_167_0
#print axioms conditional_167_0

theorem selected_168_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [168])) := by rfl

theorem source_168_0 (code : Nat) :
    edgeSource 0 168 code = 373248+code/6 := by rfl

theorem target_168_0 (code : Nat) :
    edgeTarget 0 168 code = 1010880+code%7776 := by rfl

theorem block_168_0 :
    savedBlockClass (75*168+0) = some 61 ∧
    recordedClassRoot 61 = 3469 := by decide +kernel

theorem completed_168_0 (code : Nat) :
    weight completedCredit 0 168 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 0) :=
  weight_eq_context completedCredit 0 168 [] 0 0
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_168_0 direction_168.1
    direction_168.2.1 conditioned_168 code

theorem conditional_168_0 (code : Nat) :
    weight conditionalCredit 0 168 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max ((if code%7776 = 3221 then 96 else 0)) 18) :=
  weight_eq_context conditionalCredit 0 168 [] 0 18
    (fun code => (if code%7776 = 3221 then 96 else 0)) selected_168_0 direction_168.1
    direction_168.2.2 conditioned_168 code
#print axioms selected_168_0
#print axioms source_168_0
#print axioms target_168_0
#print axioms block_168_0
#print axioms completed_168_0
#print axioms conditional_168_0

theorem selected_169_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [169])) := by rfl

theorem source_169_0 (code : Nat) :
    edgeSource 0 169 code = 373248+code/6 := by rfl

theorem target_169_0 (code : Nat) :
    edgeTarget 0 169 code = 1018656+code%7776 := by rfl

theorem block_169_0 :
    savedBlockClass (75*169+0) = some 59 ∧
    recordedClassRoot 59 = 3462 := by decide +kernel

theorem completed_169_0 (code : Nat) :
    weight completedCredit 0 169 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12) :=
  weight_eq_context completedCredit 0 169 [] 0 12
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_169_0 direction_169.1
    direction_169.2.1 conditioned_169 code

theorem conditional_169_0 (code : Nat) :
    weight conditionalCredit 0 169 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16) :=
  weight_eq_context conditionalCredit 0 169 [] 0 16
    (fun code => max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) selected_169_0 direction_169.1
    direction_169.2.2 conditioned_169 code
#print axioms selected_169_0
#print axioms source_169_0
#print axioms target_169_0
#print axioms block_169_0
#print axioms completed_169_0
#print axioms conditional_169_0

theorem selected_170_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [170])) := by rfl

theorem source_170_0 (code : Nat) :
    edgeSource 0 170 code = 381024+code/6 := by rfl

theorem target_170_0 (code : Nat) :
    edgeTarget 0 170 code = 69984+code%7776 := by rfl

theorem block_170_0 :
    savedBlockClass (75*170+0) = some 78 ∧
    recordedClassRoot 78 = 3532 := by decide +kernel

theorem completed_170_0 (code : Nat) :
    weight completedCredit 0 170 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 0 170 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_170_0 direction_170.1
    direction_170.2.1 conditioned_170 code

theorem conditional_170_0 (code : Nat) :
    weight conditionalCredit 0 170 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 0 170 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_170_0 direction_170.1
    direction_170.2.2 conditioned_170 code
#print axioms selected_170_0
#print axioms source_170_0
#print axioms target_170_0
#print axioms block_170_0
#print axioms completed_170_0
#print axioms conditional_170_0

theorem selected_170_22 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 22 [] ++ [170])) := by rfl

theorem source_170_22 (code : Nat) :
    edgeSource 22 170 code = 1189728+code/6 := by rfl

theorem target_170_22 (code : Nat) :
    edgeTarget 22 170 code = 69984+code%7776 := by rfl

theorem block_170_22 :
    savedBlockClass (75*170+22) = some 78 ∧
    recordedClassRoot 78 = 3532 := by decide +kernel

theorem completed_170_22 (code : Nat) :
    weight completedCredit 22 170 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 22 170 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_170_22 direction_170.1
    direction_170.2.1 conditioned_170 code

theorem conditional_170_22 (code : Nat) :
    weight conditionalCredit 22 170 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 22 170 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_170_22 direction_170.1
    direction_170.2.2 conditioned_170 code
#print axioms selected_170_22
#print axioms source_170_22
#print axioms target_170_22
#print axioms block_170_22
#print axioms completed_170_22
#print axioms conditional_170_22

theorem selected_170_36 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 36 [] ++ [170])) := by rfl

theorem source_170_36 (code : Nat) :
    edgeSource 36 170 code = 1298592+code/6 := by rfl

theorem target_170_36 (code : Nat) :
    edgeTarget 36 170 code = 69984+code%7776 := by rfl

theorem block_170_36 :
    savedBlockClass (75*170+36) = some 78 ∧
    recordedClassRoot 78 = 3532 := by decide +kernel

theorem completed_170_36 (code : Nat) :
    weight completedCredit 36 170 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context completedCredit 36 170 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_170_36 direction_170.1
    direction_170.2.1 conditioned_170 code

theorem conditional_170_36 (code : Nat) :
    weight conditionalCredit 36 170 code =
      120*(code%6+1)+max (max 5 (emittedCredit [] code))
        (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16) :=
  weight_eq_context conditionalCredit 36 170 [] 5 16
    (fun code => (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) selected_170_36 direction_170.1
    direction_170.2.2 conditioned_170 code
#print axioms selected_170_36
#print axioms source_170_36
#print axioms target_170_36
#print axioms block_170_36
#print axioms completed_170_36
#print axioms conditional_170_36

theorem selected_171_0 :
    [] = concreteRules.filter (fun rule =>
      decide (rule.sig <:+ Snake9.History75.prefixes.getD 0 [] ++ [171])) := by rfl

theorem source_171_0 (code : Nat) :
    edgeSource 0 171 code = 381024+code/6 := by rfl

theorem target_171_0 (code : Nat) :
    edgeTarget 0 171 code = 77760+code%7776 := by rfl

theorem block_171_0 :
    savedBlockClass (75*171+0) = some 79 ∧
    recordedClassRoot 79 = 3544 := by decide +kernel

theorem completed_171_0 (code : Nat) :
    weight completedCredit 0 171 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context completedCredit 0 171 [] 0 12
    (fun code => 0) selected_171_0 direction_171.1
    direction_171.2.1 conditioned_171 code

theorem conditional_171_0 (code : Nat) :
    weight conditionalCredit 0 171 code =
      120*(code%6+1)+max (max 0 (emittedCredit [] code))
        (max (0) 12) :=
  weight_eq_context conditionalCredit 0 171 [] 0 12
    (fun code => 0) selected_171_0 direction_171.1
    direction_171.2.2 conditioned_171 code
#print axioms selected_171_0
#print axioms source_171_0
#print axioms target_171_0
#print axioms block_171_0
#print axioms completed_171_0
#print axioms conditional_171_0

end Snake9.Context101
