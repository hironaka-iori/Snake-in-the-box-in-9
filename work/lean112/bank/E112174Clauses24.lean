import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1210 = false ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1210)) (literal (valuationOf q) (1213)) (countLit q [-1]) (countLit q [-2, -5]) (count1212 q) 1 1 (meaningNeg1 q) (meaning1210 q) (meaning1213 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1210 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1210 = false ∨ valuation q 1213 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true := by
  have hs : count1212 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1211)) (literal (valuationOf q) (1214)) (countLit q [-1]) (countLit q [-2, -5]) (count1212 q) 1 2 (meaningNeg1 q) (meaning1211 q) (meaning1214 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1211 = false ∨ valuation q 1214 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1215 = true := by
  have hs : count1215 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1215)) (countLit q [-8]) (countLit q [-9]) (count1215 q) 1 (meaningNeg9 q) (meaning1215 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1215 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1215 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1216 = true := by
  have hs : count1215 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1216)) (countLit q [-8]) (countLit q [-9]) (count1215 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning1216 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1216 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 1216 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1215 = false ∨ valuationOf q 1217 = true := by
  have hs : count1217 q = (countLit q [-7]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8, -9])
  have hm := merge_right (literal (valuationOf q) (1215)) (literal (valuationOf q) (1217)) (countLit q [-7]) (countLit q [-8, -9]) (count1217 q) 1 (meaning1215 q) (meaning1217 q) hs
  change valuationOf q 1215 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1215 = false ∨ valuation q 1217 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1216 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-7]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8, -9])
  have hm := merge_right (literal (valuationOf q) (1216)) (literal (valuationOf q) (1218)) (countLit q [-7]) (countLit q [-8, -9]) (count1217 q) 2 (meaning1216 q) (meaning1218 q) hs
  change valuationOf q 1216 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1216 = false ∨ valuation q 1218 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1215 = false ∨ valuationOf q 1218 = true := by
  have hs : count1217 q = (countLit q [-7]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8, -9])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1215)) (literal (valuationOf q) (1218)) (countLit q [-7]) (countLit q [-8, -9]) (count1217 q) 1 1 (meaningNeg7 q) (meaning1215 q) (meaning1218 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1215 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1215 = false ∨ valuation q 1218 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1216 = false ∨ valuationOf q 1219 = true := by
  have hs : count1217 q = (countLit q [-7]) + (countLit q [-8, -9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-8, -9])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1219)) (countLit q [-7]) (countLit q [-8, -9]) (count1217 q) 1 2 (meaningNeg7 q) (meaning1216 q) (meaning1219 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1219 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1216 = false ∨ valuation q 1219 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1217 = false ∨ valuationOf q 1220 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_right (literal (valuationOf q) (1217)) (literal (valuationOf q) (1220)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 1 (meaning1217 q) (meaning1220 q) hs
  change valuationOf q 1217 = false ∨ valuationOf q 1220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1217 = false ∨ valuation q 1220 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1218 = false ∨ valuationOf q 1221 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_right (literal (valuationOf q) (1218)) (literal (valuationOf q) (1221)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 2 (meaning1218 q) (meaning1221 q) hs
  change valuationOf q 1218 = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1218 = false ∨ valuation q 1221 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1219 = false ∨ valuationOf q 1222 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_right (literal (valuationOf q) (1219)) (literal (valuationOf q) (1222)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 3 (meaning1219 q) (meaning1222 q) hs
  change valuationOf q 1219 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1219 = false ∨ valuation q 1222 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1221 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1221)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 1 1 (meaning1212 q) (meaning1217 q) (meaning1221 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1217 = false ∨ valuation q 1221 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1222 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1222)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 1 2 (meaning1212 q) (meaning1218 q) (meaning1222 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1218 = false ∨ valuation q 1222 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1223 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1212)) (literal (valuationOf q) (1219)) (literal (valuationOf q) (1223)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 1 3 (meaning1212 q) (meaning1219 q) (meaning1223 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1219 = false ∨ valuation q 1223 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1222 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1213)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1222)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 2 1 (meaning1213 q) (meaning1217 q) (meaning1222 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1217 = false ∨ valuation q 1222 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1223 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1213)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1223)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 2 2 (meaning1213 q) (meaning1218 q) (meaning1223 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1218 = false ∨ valuation q 1223 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1223 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1214)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1223)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 3 1 (meaning1214 q) (meaning1217 q) (meaning1223 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1217 = false ∨ valuation q 1223 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1224 = true := by
  have hs : count1220 q = (countLit q [-1, -2, -5]) + (countLit q [-7, -8, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5]) (l₂ := [-7, -8, -9])
  have hm := merge_two (literal (valuationOf q) (1214)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1224)) (countLit q [-1, -2, -5]) (countLit q [-7, -8, -9]) (count1220 q) 3 2 (meaning1214 q) (meaning1218 q) (meaning1224 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1218 = false ∨ valuation q 1224 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1226 = true := by
  have hs : count1226 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1226)) (countLit q [-13]) (countLit q [-15]) (count1226 q) 1 (meaningNeg15 q) (meaning1226 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1226 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1226 = true := by
  have hs : count1226 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1226)) (countLit q [-13]) (countLit q [-15]) (count1226 q) 1 (meaningNeg13 q) (meaning1226 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1226 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1227 = true := by
  have hs : count1226 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1227)) (countLit q [-13]) (countLit q [-15]) (count1226 q) 1 1 (meaningNeg13 q) (meaningNeg15 q) (meaning1227 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1227 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 1227 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1227 = false ∨ valuationOf q 1229 = true := by
  have hs : count1228 q = (countLit q [-11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1227)) (literal (valuationOf q) (1229)) (countLit q [-11]) (countLit q [-13, -15]) (count1228 q) 2 (meaning1227 q) (meaning1229 q) hs
  change valuationOf q 1227 = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1227 = false ∨ valuation q 1229 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1228 = true := by
  have hs : count1228 q = (countLit q [-11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1228)) (countLit q [-11]) (countLit q [-13, -15]) (count1228 q) 1 (meaningNeg11 q) (meaning1228 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1228 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1228 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1226 = false ∨ valuationOf q 1229 = true := by
  have hs : count1228 q = (countLit q [-11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (1226)) (literal (valuationOf q) (1229)) (countLit q [-11]) (countLit q [-13, -15]) (count1228 q) 1 1 (meaningNeg11 q) (meaning1226 q) (meaning1229 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1226 = false ∨ valuationOf q 1229 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1226 = false ∨ valuation q 1229 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1227 = false ∨ valuationOf q 1230 = true := by
  have hs : count1228 q = (countLit q [-11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (1227)) (literal (valuationOf q) (1230)) (countLit q [-11]) (countLit q [-13, -15]) (count1228 q) 1 2 (meaningNeg11 q) (meaning1227 q) (meaning1230 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1227 = false ∨ valuationOf q 1230 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1227 = false ∨ valuation q 1230 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1231 = true := by
  have hs : count1231 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1231)) (countLit q [-19]) (countLit q [-20]) (count1231 q) 1 (meaningNeg20 q) (meaning1231 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1231 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1231 = true := by
  have hs : count1231 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1231)) (countLit q [-19]) (countLit q [-20]) (count1231 q) 1 (meaningNeg19 q) (meaning1231 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1231 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 20 = true ∨ valuationOf q 1232 = true := by
  have hs : count1231 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (1232)) (countLit q [-19]) (countLit q [-20]) (count1231 q) 1 1 (meaningNeg19 q) (meaningNeg20 q) (meaning1232 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 1232 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 20 = true ∨ valuation q 1232 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1233)) (countLit q [-23]) (countLit q [-24]) (count1233 q) 1 (meaningNeg24 q) (meaning1233 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1233 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1233)) (countLit q [-23]) (countLit q [-24]) (count1233 q) 1 (meaningNeg23 q) (meaning1233 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1233 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-19, -20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (1233)) (literal (valuationOf q) (1235)) (countLit q [-19, -20]) (countLit q [-23, -24]) (count1235 q) 1 (meaning1233 q) (meaning1235 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1235 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-19, -20]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (1231)) (literal (valuationOf q) (1235)) (countLit q [-19, -20]) (countLit q [-23, -24]) (count1235 q) 1 (meaning1231 q) (meaning1235 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1235 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E174.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112174
