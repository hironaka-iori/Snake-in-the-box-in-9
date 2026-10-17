import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (895)) (countLit q [-25]) (countLit q [-27]) (count895 q) 1 (meaningNeg25 q) (meaning895 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 895 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 27 = true ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (896)) (countLit q [-25]) (countLit q [-27]) (count895 q) 1 1 (meaningNeg25 q) (meaningNeg27 q) (meaning896 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 896 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 897 = true := by
  have hs : count897 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (897)) (countLit q [-28]) (countLit q [-31]) (count897 q) 1 (meaningNeg31 q) (meaning897 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 897 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 897 = true := by
  have hs : count897 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (897)) (countLit q [-28]) (countLit q [-31]) (count897 q) 1 (meaningNeg28 q) (meaning897 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 897 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 898 = true := by
  have hs : count897 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (898)) (countLit q [-28]) (countLit q [-31]) (count897 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning898 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 898 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 899 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (897)) (literal (valuationOf q) (899)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 1 (meaning897 q) (meaning899 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 899 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 900 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (898)) (literal (valuationOf q) (900)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 2 (meaning898 q) (meaning900 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 900 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 899 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (895)) (literal (valuationOf q) (899)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 1 (meaning895 q) (meaning899 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 899 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 897 = false ∨ valuationOf q 900 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (897)) (literal (valuationOf q) (900)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 1 1 (meaning895 q) (meaning897 q) (meaning900 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 897 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 897 = false ∨ valuation q 900 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 898 = false ∨ valuationOf q 901 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (898)) (literal (valuationOf q) (901)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 1 2 (meaning895 q) (meaning898 q) (meaning901 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 898 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 898 = false ∨ valuation q 901 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 900 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (896)) (literal (valuationOf q) (900)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 2 (meaning896 q) (meaning900 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 900 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 897 = false ∨ valuationOf q 901 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (897)) (literal (valuationOf q) (901)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 2 1 (meaning896 q) (meaning897 q) (meaning901 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 897 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 897 = false ∨ valuation q 901 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 898 = false ∨ valuationOf q 902 = true := by
  have hs : count899 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (898)) (literal (valuationOf q) (902)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count899 q) 2 2 (meaning896 q) (meaning898 q) (meaning902 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 898 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 898 = false ∨ valuation q 902 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 903 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (899)) (literal (valuationOf q) (903)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 1 (meaning899 q) (meaning903 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 903 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 904 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (900)) (literal (valuationOf q) (904)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 2 (meaning900 q) (meaning904 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 904 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 905 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (901)) (literal (valuationOf q) (905)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 3 (meaning901 q) (meaning905 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 905 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 906 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (902)) (literal (valuationOf q) (906)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 4 (meaning902 q) (meaning906 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 906 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 903 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (891)) (literal (valuationOf q) (903)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 1 (meaning891 q) (meaning903 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 903 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 899 = false ∨ valuationOf q 904 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (899)) (literal (valuationOf q) (904)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 1 1 (meaning891 q) (meaning899 q) (meaning904 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 899 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 899 = false ∨ valuation q 904 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 900 = false ∨ valuationOf q 905 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (900)) (literal (valuationOf q) (905)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 1 2 (meaning891 q) (meaning900 q) (meaning905 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 900 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 900 = false ∨ valuation q 905 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 901 = false ∨ valuationOf q 906 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (901)) (literal (valuationOf q) (906)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 1 3 (meaning891 q) (meaning901 q) (meaning906 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 901 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 901 = false ∨ valuation q 906 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 902 = false ∨ valuationOf q 907 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (902)) (literal (valuationOf q) (907)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 1 4 (meaning891 q) (meaning902 q) (meaning907 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 902 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 902 = false ∨ valuation q 907 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 904 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (892)) (literal (valuationOf q) (904)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 2 (meaning892 q) (meaning904 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 904 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 899 = false ∨ valuationOf q 905 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (899)) (literal (valuationOf q) (905)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 2 1 (meaning892 q) (meaning899 q) (meaning905 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 899 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 899 = false ∨ valuation q 905 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 900 = false ∨ valuationOf q 906 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (900)) (literal (valuationOf q) (906)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 2 2 (meaning892 q) (meaning900 q) (meaning906 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 900 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 900 = false ∨ valuation q 906 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 901 = false ∨ valuationOf q 907 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (901)) (literal (valuationOf q) (907)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 2 3 (meaning892 q) (meaning901 q) (meaning907 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 901 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 901 = false ∨ valuation q 907 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 902 = false ∨ valuationOf q 908 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (902)) (literal (valuationOf q) (908)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 2 4 (meaning892 q) (meaning902 q) (meaning908 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 902 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 902 = false ∨ valuation q 908 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 905 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (893)) (literal (valuationOf q) (905)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 3 (meaning893 q) (meaning905 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 905 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 899 = false ∨ valuationOf q 906 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (899)) (literal (valuationOf q) (906)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 3 1 (meaning893 q) (meaning899 q) (meaning906 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 899 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 899 = false ∨ valuation q 906 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 900 = false ∨ valuationOf q 907 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (900)) (literal (valuationOf q) (907)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 3 2 (meaning893 q) (meaning900 q) (meaning907 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 900 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 900 = false ∨ valuation q 907 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 901 = false ∨ valuationOf q 908 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (901)) (literal (valuationOf q) (908)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 3 3 (meaning893 q) (meaning901 q) (meaning908 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 901 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 901 = false ∨ valuation q 908 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 902 = false ∨ valuationOf q 909 = true := by
  have hs : count903 q = (countLit q [-15, -19, -22, -24]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-15, -19, -22, -24]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (902)) (literal (valuationOf q) (909)) (countLit q [-15, -19, -22, -24]) (countLit q [-25, -27, -28, -31]) (count903 q) 3 4 (meaning893 q) (meaning902 q) (meaning909 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 902 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 902 = false ∨ valuation q 909 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E121.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112121
