import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1483 = true := by
  have hs : count1477 q = (countLit q [-2, -3, -7, -8, -11, -13, -15]) + (countLit q [-17, -19, -22, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15]) (l₂ := [-17, -19, -22, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1483)) (countLit q [-2, -3, -7, -8, -11, -13, -15]) (countLit q [-17, -19, -22, -23, -24, -27, -29]) (count1477 q) 5 2 (meaning1454 q) (meaning1471 q) (meaning1483 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1471 = false ∨ valuation q 1483 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1484 = true := by
  have hs : count1477 q = (countLit q [-2, -3, -7, -8, -11, -13, -15]) + (countLit q [-17, -19, -22, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15]) (l₂ := [-17, -19, -22, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1484)) (countLit q [-2, -3, -7, -8, -11, -13, -15]) (countLit q [-17, -19, -22, -23, -24, -27, -29]) (count1477 q) 5 3 (meaning1454 q) (meaning1472 q) (meaning1484 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1472 = false ∨ valuation q 1484 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1485 = true := by
  have hs : count1477 q = (countLit q [-2, -3, -7, -8, -11, -13, -15]) + (countLit q [-17, -19, -22, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15]) (l₂ := [-17, -19, -22, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1485)) (countLit q [-2, -3, -7, -8, -11, -13, -15]) (countLit q [-17, -19, -22, -23, -24, -27, -29]) (count1477 q) 5 4 (meaning1454 q) (meaning1473 q) (meaning1485 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1473 = false ∨ valuation q 1485 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1491)) (countLit q [-35]) (countLit q [-38]) (count1491 q) 1 (meaningNeg38 q) (meaning1491 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1491 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1491 = true := by
  have hs : count1491 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1491)) (countLit q [-35]) (countLit q [-38]) (count1491 q) 1 (meaningNeg35 q) (meaning1491 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1491 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1492 = true := by
  have hs : count1491 q = (countLit q [-35]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1492)) (countLit q [-35]) (countLit q [-38]) (count1491 q) 1 1 (meaningNeg35 q) (meaningNeg38 q) (meaning1492 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 38 = true ∨ valuation q 1492 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1493 = true := by
  have hs : count1493 q = (countLit q [-32]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -38])
  have hm := merge_right (literal (valuationOf q) (1491)) (literal (valuationOf q) (1493)) (countLit q [-32]) (countLit q [-35, -38]) (count1493 q) 1 (meaning1491 q) (meaning1493 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1493 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = true := by
  have hs : count1493 q = (countLit q [-32]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -38])
  have hm := merge_right (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (countLit q [-32]) (countLit q [-35, -38]) (count1493 q) 2 (meaning1492 q) (meaning1494 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1493 = true := by
  have hs : count1493 q = (countLit q [-32]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -38])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1493)) (countLit q [-32]) (countLit q [-35, -38]) (count1493 q) 1 (meaningNeg32 q) (meaning1493 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1493 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1491 = false ∨ valuationOf q 1494 = true := by
  have hs : count1493 q = (countLit q [-32]) + (countLit q [-35, -38]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35, -38])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1494)) (countLit q [-32]) (countLit q [-35, -38]) (count1493 q) 1 1 (meaningNeg32 q) (meaning1491 q) (meaning1494 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1491 = false ∨ valuation q 1494 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1496)) (countLit q [-39]) (countLit q [-41]) (count1496 q) 1 (meaningNeg41 q) (meaning1496 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1496 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1496)) (countLit q [-39]) (countLit q [-41]) (count1496 q) 1 (meaningNeg39 q) (meaning1496 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1496 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1498 = true := by
  have hs : count1498 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1498)) (countLit q [-45]) (countLit q [-46]) (count1498 q) 1 (meaningNeg46 q) (meaning1498 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1498 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1498 = true := by
  have hs : count1498 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1498)) (countLit q [-45]) (countLit q [-46]) (count1498 q) 1 (meaningNeg45 q) (meaning1498 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1498 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1499)) (countLit q [-45]) (countLit q [-46]) (count1498 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning1499 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 1499 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-39, -41]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1500)) (countLit q [-39, -41]) (countLit q [-45, -46]) (count1500 q) 1 (meaning1498 q) (meaning1500 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1500 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-39, -41]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1499)) (literal (valuationOf q) (1501)) (countLit q [-39, -41]) (countLit q [-45, -46]) (count1500 q) 2 (meaning1499 q) (meaning1501 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1501 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-39, -41]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-45, -46])
  have hm := merge_left (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-39, -41]) (countLit q [-45, -46]) (count1500 q) 1 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-39, -41]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1501)) (countLit q [-39, -41]) (countLit q [-45, -46]) (count1500 q) 1 1 (meaning1496 q) (meaning1498 q) (meaning1501 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1498 = false ∨ valuation q 1501 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true := by
  have hs : count1500 q = (countLit q [-39, -41]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-39, -41]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1502)) (countLit q [-39, -41]) (countLit q [-45, -46]) (count1500 q) 1 2 (meaning1496 q) (meaning1499 q) (meaning1502 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1499 = false ∨ valuation q 1502 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1504)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 1 (meaning1500 q) (meaning1504 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1504 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1505)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 2 (meaning1501 q) (meaning1505 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1505 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 3 (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1506 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1504)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 1 (meaning1493 q) (meaning1504 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1504 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1505)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 1 1 (meaning1493 q) (meaning1500 q) (meaning1505 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1500 = false ∨ valuation q 1505 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1506 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1506)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 1 2 (meaning1493 q) (meaning1501 q) (meaning1506 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1501 = false ∨ valuation q 1506 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1507 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1507)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 1 3 (meaning1493 q) (meaning1502 q) (meaning1507 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1502 = false ∨ valuation q 1507 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_left (literal (valuationOf q) (1494)) (literal (valuationOf q) (1505)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 2 (meaning1494 q) (meaning1505 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1505 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1506 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1506)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 2 1 (meaning1494 q) (meaning1500 q) (meaning1506 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1500 = false ∨ valuation q 1506 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1507 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1507)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 2 2 (meaning1494 q) (meaning1501 q) (meaning1507 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1501 = false ∨ valuation q 1507 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1508 = true := by
  have hs : count1504 q = (countLit q [-32, -35, -38]) + (countLit q [-39, -41, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38]) (l₂ := [-39, -41, -45, -46])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1508)) (countLit q [-32, -35, -38]) (countLit q [-39, -41, -45, -46]) (count1504 q) 2 3 (meaning1494 q) (meaning1502 q) (meaning1508 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1502 = false ∨ valuation q 1508 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-48]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1511)) (countLit q [-48]) (countLit q [-52]) (count1511 q) 1 (meaningNeg52 q) (meaning1511 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1511 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E027.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112027
