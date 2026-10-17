import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (854)) (countLit q [-6]) (countLit q [-7]) (count854 q) 1 (meaningNeg6 q) (meaning854 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 854 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (855)) (countLit q [-6]) (countLit q [-7]) (count854 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning855 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 855 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (856)) (countLit q [-10]) (countLit q [-12]) (count856 q) 1 (meaningNeg12 q) (meaning856 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 856 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (856)) (countLit q [-10]) (countLit q [-12]) (count856 q) 1 (meaningNeg10 q) (meaning856 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 856 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 12 = true ∨ valuationOf q 857 = true := by
  have hs : count856 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (857)) (countLit q [-10]) (countLit q [-12]) (count856 q) 1 1 (meaningNeg10 q) (meaningNeg12 q) (meaning857 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 857 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 1 (meaning856 q) (meaning858 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 859 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (857)) (literal (valuationOf q) (859)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 2 (meaning857 q) (meaning859 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 859 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (854)) (literal (valuationOf q) (858)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 1 (meaning854 q) (meaning858 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 858 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 856 = false ∨ valuationOf q 859 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (856)) (literal (valuationOf q) (859)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 1 1 (meaning854 q) (meaning856 q) (meaning859 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 856 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 856 = false ∨ valuation q 859 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 857 = false ∨ valuationOf q 860 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (857)) (literal (valuationOf q) (860)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 1 2 (meaning854 q) (meaning857 q) (meaning860 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 857 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 857 = false ∨ valuation q 860 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 859 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (855)) (literal (valuationOf q) (859)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 2 (meaning855 q) (meaning859 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 859 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 856 = false ∨ valuationOf q 860 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (856)) (literal (valuationOf q) (860)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 2 1 (meaning855 q) (meaning856 q) (meaning860 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 856 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 856 = false ∨ valuation q 860 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 857 = false ∨ valuationOf q 861 = true := by
  have hs : count858 q = (countLit q [-6, -7]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (857)) (literal (valuationOf q) (861)) (countLit q [-6, -7]) (countLit q [-10, -12]) (count858 q) 2 2 (meaning855 q) (meaning857 q) (meaning861 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 857 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 857 = false ∨ valuation q 861 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_right (literal (valuationOf q) (858)) (literal (valuationOf q) (862)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 1 (meaning858 q) (meaning862 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 862 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_right (literal (valuationOf q) (859)) (literal (valuationOf q) (863)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 2 (meaning859 q) (meaning863 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 863 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 3 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 4 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (851)) (literal (valuationOf q) (862)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 1 (meaning851 q) (meaning862 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 862 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 858 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (858)) (literal (valuationOf q) (863)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 1 1 (meaning851 q) (meaning858 q) (meaning863 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 858 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 858 = false ∨ valuation q 863 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 859 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (859)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 1 2 (meaning851 q) (meaning859 q) (meaning864 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 859 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 859 = false ∨ valuation q 864 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (860)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 1 3 (meaning851 q) (meaning860 q) (meaning865 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 860 = false ∨ valuation q 865 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (861)) (literal (valuationOf q) (866)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 1 4 (meaning851 q) (meaning861 q) (meaning866 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 861 = false ∨ valuation q 866 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (852)) (literal (valuationOf q) (863)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 2 (meaning852 q) (meaning863 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 863 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 858 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (858)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 2 1 (meaning852 q) (meaning858 q) (meaning864 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 858 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 858 = false ∨ valuation q 864 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 859 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (859)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 2 2 (meaning852 q) (meaning859 q) (meaning865 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 859 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 859 = false ∨ valuation q 865 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (860)) (literal (valuationOf q) (866)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 2 3 (meaning852 q) (meaning860 q) (meaning866 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 860 = false ∨ valuation q 866 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (852)) (literal (valuationOf q) (861)) (literal (valuationOf q) (867)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 2 4 (meaning852 q) (meaning861 q) (meaning867 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 861 = false ∨ valuation q 867 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 864 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_left (literal (valuationOf q) (853)) (literal (valuationOf q) (864)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 3 (meaning853 q) (meaning864 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 864 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 858 = false ∨ valuationOf q 865 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (858)) (literal (valuationOf q) (865)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 3 1 (meaning853 q) (meaning858 q) (meaning865 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 858 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 858 = false ∨ valuation q 865 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 859 = false ∨ valuationOf q 866 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (859)) (literal (valuationOf q) (866)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 3 2 (meaning853 q) (meaning859 q) (meaning866 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 859 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 859 = false ∨ valuation q 866 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true := by
  have hs : count862 q = (countLit q [-1, -2, -5]) + (countLit q [-6, -7, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-6, -7, -10, -12])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (860)) (literal (valuationOf q) (867)) (countLit q [-1, -2, -5]) (countLit q [-6, -7, -10, -12]) (count862 q) 3 3 (meaning853 q) (meaning860 q) (meaning867 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 860 = false ∨ valuation q 867 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-15]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (869)) (countLit q [-15]) (countLit q [-16]) (count869 q) 1 (meaningNeg16 q) (meaning869 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 869 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E260.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112260
