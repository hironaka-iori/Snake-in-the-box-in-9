import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43, -44])
  have hm := merge_right (literal (valuationOf q) (1300)) (literal (valuationOf q) (1302)) (countLit q [-42]) (countLit q [-43, -44]) (count1301 q) 2 (meaning1300 q) (meaning1302 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1302 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1301)) (countLit q [-42]) (countLit q [-43, -44]) (count1301 q) 1 (meaningNeg42 q) (meaning1301 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1301 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1299 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-42]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1302)) (countLit q [-42]) (countLit q [-43, -44]) (count1301 q) 1 1 (meaningNeg42 q) (meaning1299 q) (meaning1302 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1299 = false ∨ valuation q 1302 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1304)) (countLit q [-45]) (countLit q [-49]) (count1304 q) 1 (meaningNeg49 q) (meaning1304 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1304 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1304 = true := by
  have hs : count1304 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1304)) (countLit q [-45]) (countLit q [-49]) (count1304 q) 1 (meaningNeg45 q) (meaning1304 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1304 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1305 = true := by
  have hs : count1304 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1305)) (countLit q [-45]) (countLit q [-49]) (count1304 q) 1 1 (meaningNeg45 q) (meaningNeg49 q) (meaning1305 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 1305 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1306)) (countLit q [-50]) (countLit q [-53]) (count1306 q) 1 (meaningNeg50 q) (meaning1306 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1306 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_left (literal (valuationOf q) (1304)) (literal (valuationOf q) (1308)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1308 q) 1 (meaning1304 q) (meaning1308 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1308 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1309)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1308 q) 1 1 (meaning1304 q) (meaning1306 q) (meaning1309 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1306 = false ∨ valuation q 1309 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1305 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_left (literal (valuationOf q) (1305)) (literal (valuationOf q) (1309)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1308 q) 2 (meaning1305 q) (meaning1309 q) hs
  change valuationOf q 1305 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1305 = false ∨ valuation q 1309 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1305 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1310 = true := by
  have hs : count1308 q = (countLit q [-45, -49]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (1305)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1310)) (countLit q [-45, -49]) (countLit q [-50, -53]) (count1308 q) 2 1 (meaning1305 q) (meaning1306 q) (meaning1310 q) hs
  change valuationOf q 1305 = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1305 = false ∨ valuation q 1306 = false ∨ valuation q 1310 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1312)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 1 (meaning1308 q) (meaning1312 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1312 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_right (literal (valuationOf q) (1309)) (literal (valuationOf q) (1313)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 2 (meaning1309 q) (meaning1313 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1313 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1314 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_right (literal (valuationOf q) (1310)) (literal (valuationOf q) (1314)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 3 (meaning1310 q) (meaning1314 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1314 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1312 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_left (literal (valuationOf q) (1301)) (literal (valuationOf q) (1312)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 1 (meaning1301 q) (meaning1312 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1312 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1313)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 1 1 (meaning1301 q) (meaning1308 q) (meaning1313 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1308 = false ∨ valuation q 1313 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1314 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1314)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 1 2 (meaning1301 q) (meaning1309 q) (meaning1314 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1309 = false ∨ valuation q 1314 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1313 = true := by
  have hs : count1312 q = (countLit q [-42, -43, -44]) + (countLit q [-45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-42, -43, -44]) (l₂ := [-45, -49, -50, -53])
  have hm := merge_left (literal (valuationOf q) (1302)) (literal (valuationOf q) (1313)) (countLit q [-42, -43, -44]) (countLit q [-45, -49, -50, -53]) (count1312 q) 2 (meaning1302 q) (meaning1313 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1313 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_right (literal (valuationOf q) (1312)) (literal (valuationOf q) (1319)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 1 (meaning1312 q) (meaning1319 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1319 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_right (literal (valuationOf q) (1313)) (literal (valuationOf q) (1320)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 2 (meaning1313 q) (meaning1320 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1320 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_right (literal (valuationOf q) (1314)) (literal (valuationOf q) (1321)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 3 (meaning1314 q) (meaning1321 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1321 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_left (literal (valuationOf q) (1293)) (literal (valuationOf q) (1319)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 1 (meaning1293 q) (meaning1319 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1319 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1320)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 1 1 (meaning1293 q) (meaning1312 q) (meaning1320 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1312 = false ∨ valuation q 1320 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1321)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 1 2 (meaning1293 q) (meaning1313 q) (meaning1321 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1313 = false ∨ valuation q 1321 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1322 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1293)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1322)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 1 3 (meaning1293 q) (meaning1314 q) (meaning1322 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1314 = false ∨ valuation q 1322 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_left (literal (valuationOf q) (1294)) (literal (valuationOf q) (1320)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 2 (meaning1294 q) (meaning1320 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1320 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1312)) (literal (valuationOf q) (1321)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 2 1 (meaning1294 q) (meaning1312 q) (meaning1321 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1312 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1312 = false ∨ valuation q 1321 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1322 = true := by
  have hs : count1319 q = (countLit q [-27, -30, -33, -35, -36, -38]) + (countLit q [-42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -36, -38]) (l₂ := [-42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1294)) (literal (valuationOf q) (1313)) (literal (valuationOf q) (1322)) (countLit q [-27, -30, -33, -35, -36, -38]) (countLit q [-42, -43, -44, -45, -49, -50, -53]) (count1319 q) 2 2 (meaning1294 q) (meaning1313 q) (meaning1322 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1313 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1313 = false ∨ valuation q 1322 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1330 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1319)) (literal (valuationOf q) (1330)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 1 1 (meaning1273 q) (meaning1319 q) (meaning1330 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1319 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1319 = false ∨ valuation q 1330 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 1 2 (meaning1273 q) (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1320 = false ∨ valuation q 1331 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1332 = true := by
  have hs : count1329 q = (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) + (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (l₂ := [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1332)) (countLit q [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]) (countLit q [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]) (count1329 q) 1 3 (meaning1273 q) (meaning1321 q) (meaning1332 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1321 = false ∨ valuation q 1332 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E175.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112175
