import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (859)) (literal (valuationOf q) (863)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 2 (meaning859 q) (meaning863 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 863 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 3 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 4 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (851)) (literal (valuationOf q) (862)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 1 (meaning851 q) (meaning862 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 862 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 858 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (858)) (literal (valuationOf q) (863)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 1 1 (meaning851 q) (meaning858 q) (meaning863 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 858 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 858 = false ∨ valuation q 863 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 859 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (859)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 1 2 (meaning851 q) (meaning859 q) (meaning864 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 859 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 859 = false ∨ valuation q 864 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (860)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 1 3 (meaning851 q) (meaning860 q) (meaning865 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 860 = false ∨ valuation q 865 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (861)) (literal (valuationOf q) (866)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 1 4 (meaning851 q) (meaning861 q) (meaning866 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 861 = false ∨ valuation q 866 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (852)) (literal (valuationOf q) (863)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 2 (meaning852 q) (meaning863 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 863 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 858 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (858)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 2 1 (meaning852 q) (meaning858 q) (meaning864 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 858 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 858 = false ∨ valuation q 864 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 859 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (859)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 2 2 (meaning852 q) (meaning859 q) (meaning865 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 859 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 859 = false ∨ valuation q 865 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (860)) (literal (valuationOf q) (866)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 2 3 (meaning852 q) (meaning860 q) (meaning866 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 860 = false ∨ valuation q 866 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (861)) (literal (valuationOf q) (867)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 2 4 (meaning852 q) (meaning861 q) (meaning867 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 861 = false ∨ valuation q 867 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (853)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 3 (meaning853 q) (meaning864 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 864 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 858 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (858)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 3 1 (meaning853 q) (meaning858 q) (meaning865 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 858 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 858 = false ∨ valuation q 865 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 859 = false ∨ valuationOf q 866 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (859)) (literal (valuationOf q) (866)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 3 2 (meaning853 q) (meaning859 q) (meaning866 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 859 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 859 = false ∨ valuation q 866 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (860)) (literal (valuationOf q) (867)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 3 3 (meaning853 q) (meaning860 q) (meaning867 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 860 = false ∨ valuation q 867 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (861)) (literal (valuationOf q) (868)) (countLit q [-1, -2, -5]) (countLit q [-7, -10, -11, -14]) (count862 q) 3 4 (meaning853 q) (meaning861 q) (meaning868 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 861 = false ∨ valuation q 868 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (869)) (countLit q [-15]) (countLit q [-18]) (count869 q) 1 (meaningNeg18 q) (meaning869 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 869 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (869)) (countLit q [-15]) (countLit q [-18]) (count869 q) 1 (meaningNeg15 q) (meaning869 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 869 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 18 = true ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (870)) (countLit q [-15]) (countLit q [-18]) (count869 q) 1 1 (meaningNeg15 q) (meaningNeg18 q) (meaning870 q) hs
  change (! (valuationOf q 15)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 870 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (871)) (countLit q [-19]) (countLit q [-21]) (count871 q) 1 (meaningNeg21 q) (meaning871 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 871 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (871)) (countLit q [-19]) (countLit q [-21]) (count871 q) 1 (meaningNeg19 q) (meaning871 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 871 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 21 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (872)) (countLit q [-19]) (countLit q [-21]) (count871 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning872 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 872 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 1 (meaning871 q) (meaning873 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 2 (meaning872 q) (meaning874 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (873)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 1 (meaning869 q) (meaning873 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 873 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 1 1 (meaning869 q) (meaning871 q) (meaning874 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 871 = false ∨ valuation q 874 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (872)) (literal (valuationOf q) (875)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 1 2 (meaning869 q) (meaning872 q) (meaning875 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 872 = false ∨ valuation q 875 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 2 (meaning870 q) (meaning874 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 874 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 2 1 (meaning870 q) (meaning871 q) (meaning875 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 871 = false ∨ valuation q 875 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count873 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count873 q) 2 2 (meaning870 q) (meaning872 q) (meaning876 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 872 = false ∨ valuation q 876 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E256.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112256
