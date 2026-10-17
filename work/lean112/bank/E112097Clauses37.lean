import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1002)) (countLit q [-89]) (countLit q [-91]) (count1002 q) 1 (meaningNeg91 q) (meaning1002 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1002 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1002)) (countLit q [-89]) (countLit q [-91]) (count1002 q) 1 (meaningNeg89 q) (meaning1002 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1002 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1003 = true := by
  have hs : count1002 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1003)) (countLit q [-89]) (countLit q [-91]) (count1002 q) 1 1 (meaningNeg89 q) (meaningNeg91 q) (meaning1003 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 1003 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1004 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1002)) (literal (valuationOf q) (1004)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 1 (meaning1002 q) (meaning1004 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1004 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1003)) (literal (valuationOf q) (1005)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 2 (meaning1003 q) (meaning1005 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1005 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1004 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1000)) (literal (valuationOf q) (1004)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 1 (meaning1000 q) (meaning1004 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1004 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1000)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1005)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 1 1 (meaning1000 q) (meaning1002 q) (meaning1005 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1002 = false ∨ valuation q 1005 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1006 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1000)) (literal (valuationOf q) (1003)) (literal (valuationOf q) (1006)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 1 2 (meaning1000 q) (meaning1003 q) (meaning1006 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1003 = false ∨ valuation q 1006 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1005 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1001)) (literal (valuationOf q) (1005)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 2 (meaning1001 q) (meaning1005 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1005 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1006 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1002)) (literal (valuationOf q) (1006)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 2 1 (meaning1001 q) (meaning1002 q) (meaning1006 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1002 = false ∨ valuationOf q 1006 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1002 = false ∨ valuation q 1006 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1007 = true := by
  have hs : count1004 q = (countLit q [-86, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1003)) (literal (valuationOf q) (1007)) (countLit q [-86, -87]) (countLit q [-89, -91]) (count1004 q) 2 2 (meaning1001 q) (meaning1003 q) (meaning1007 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1003 = false ∨ valuationOf q 1007 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1003 = false ∨ valuation q 1007 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1004)) (literal (valuationOf q) (1008)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 1 (meaning1004 q) (meaning1008 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1008 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1005)) (literal (valuationOf q) (1009)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 2 (meaning1005 q) (meaning1009 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1009 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1006)) (literal (valuationOf q) (1010)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 3 (meaning1006 q) (meaning1010 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1010 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1007 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1007)) (literal (valuationOf q) (1011)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 4 (meaning1007 q) (meaning1011 q) hs
  change valuationOf q 1007 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1007 = false ∨ valuation q 1011 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1008 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (996)) (literal (valuationOf q) (1008)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 1 (meaning996 q) (meaning1008 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1008 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1008 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1009)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 1 1 (meaning996 q) (meaning1004 q) (meaning1009 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1004 = false ∨ valuation q 1009 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1010)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 1 2 (meaning996 q) (meaning1005 q) (meaning1010 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1005 = false ∨ valuation q 1010 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1006)) (literal (valuationOf q) (1011)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 1 3 (meaning996 q) (meaning1006 q) (meaning1011 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1006 = false ∨ valuation q 1011 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 996 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1012 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (996)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1012)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 1 4 (meaning996 q) (meaning1007 q) (meaning1012 q) hs
  change valuationOf q 996 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 996 = false ∨ valuation q 1007 = false ∨ valuation q 1012 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1009 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (997)) (literal (valuationOf q) (1009)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 2 (meaning997 q) (meaning1009 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1009 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1010)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 2 1 (meaning997 q) (meaning1004 q) (meaning1010 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1004 = false ∨ valuation q 1010 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1011)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 2 2 (meaning997 q) (meaning1005 q) (meaning1011 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1005 = false ∨ valuation q 1011 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1012 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1006)) (literal (valuationOf q) (1012)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 2 3 (meaning997 q) (meaning1006 q) (meaning1012 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1006 = false ∨ valuation q 1012 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 997 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1013 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (997)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1013)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 2 4 (meaning997 q) (meaning1007 q) (meaning1013 q) hs
  change valuationOf q 997 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 997 = false ∨ valuation q 1007 = false ∨ valuation q 1013 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1010 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (998)) (literal (valuationOf q) (1010)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 3 (meaning998 q) (meaning1010 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1010 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1010 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (998)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1011)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 3 1 (meaning998 q) (meaning1004 q) (meaning1011 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1004 = false ∨ valuation q 1011 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1012 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (998)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1012)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 3 2 (meaning998 q) (meaning1005 q) (meaning1012 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1005 = false ∨ valuation q 1012 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1013 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (998)) (literal (valuationOf q) (1006)) (literal (valuationOf q) (1013)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 3 3 (meaning998 q) (meaning1006 q) (meaning1013 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1006 = false ∨ valuation q 1013 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 998 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1014 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (998)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1014)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 3 4 (meaning998 q) (meaning1007 q) (meaning1014 q) hs
  change valuationOf q 998 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 998 = false ∨ valuation q 1007 = false ∨ valuation q 1014 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1011 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (999)) (literal (valuationOf q) (1011)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 4 (meaning999 q) (meaning1011 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1011 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1011 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1012 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (999)) (literal (valuationOf q) (1004)) (literal (valuationOf q) (1012)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 4 1 (meaning999 q) (meaning1004 q) (meaning1012 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1004 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1004 = false ∨ valuation q 1012 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E097.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112097
