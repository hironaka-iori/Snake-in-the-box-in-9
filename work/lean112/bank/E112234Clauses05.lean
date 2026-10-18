import E112234Semantics
import B112E234Inputs
namespace Snake9.Regrowth.E112234
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1211 = true := by
  have hs : count1211 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1211)) (countLit q [-22]) (countLit q [-25]) (count1211 q) 1 (meaningNeg22 q) (meaning1211 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1211 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1212 = true := by
  have hs : count1211 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1212)) (countLit q [-22]) (countLit q [-25]) (count1211 q) 1 1 (meaningNeg22 q) (meaningNeg25 q) (meaning1212 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 1212 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 1211 = false ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-20]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (1211)) (literal (valuationOf q) (1213)) (countLit q [-20]) (countLit q [-22, -25]) (count1213 q) 1 (meaning1211 q) (meaning1213 q) hs
  change valuationOf q 1211 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 1211 = false ∨ valuation q 1213 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1214 = true := by
  have hs : count1213 q = (countLit q [-20]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (1212)) (literal (valuationOf q) (1214)) (countLit q [-20]) (countLit q [-22, -25]) (count1213 q) 2 (meaning1212 q) (meaning1214 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1214 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-20]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -25])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1213)) (countLit q [-20]) (countLit q [-22, -25]) (count1213 q) 1 (meaningNeg20 q) (meaning1213 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1213 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true := by
  have hs : count1213 q = (countLit q [-20]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (1211)) (literal (valuationOf q) (1214)) (countLit q [-20]) (countLit q [-22, -25]) (count1213 q) 1 1 (meaningNeg20 q) (meaning1211 q) (meaning1214 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1211 = false ∨ valuation q 1214 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1216 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_right (literal (valuationOf q) (1213)) (literal (valuationOf q) (1216)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 1 (meaning1213 q) (meaning1216 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1216 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1216 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_right (literal (valuationOf q) (1214)) (literal (valuationOf q) (1217)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 2 (meaning1214 q) (meaning1217 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1217 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1208)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1217)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 1 1 (meaning1208 q) (meaning1213 q) (meaning1217 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1213 = false ∨ valuation q 1217 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1218 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1208)) (literal (valuationOf q) (1214)) (literal (valuationOf q) (1218)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 1 2 (meaning1208 q) (meaning1214 q) (meaning1218 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1214 = false ∨ valuation q 1218 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1218 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1209)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1218)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 2 1 (meaning1209 q) (meaning1213 q) (meaning1218 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1213 = false ∨ valuation q 1218 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1219 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1209)) (literal (valuationOf q) (1214)) (literal (valuationOf q) (1219)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 2 2 (meaning1209 q) (meaning1214 q) (meaning1219 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1214 = false ∨ valuation q 1219 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 1210 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1219 = true := by
  have hs : count1216 q = (countLit q [-14, -16, -19]) + (countLit q [-20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -19]) (l₂ := [-20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1210)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1219)) (countLit q [-14, -16, -19]) (countLit q [-20, -22, -25]) (count1216 q) 3 1 (meaning1210 q) (meaning1213 q) (meaning1219 q) hs
  change valuationOf q 1210 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 1210 = false ∨ valuation q 1213 = false ∨ valuation q 1219 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 1217 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_right (literal (valuationOf q) (1217)) (literal (valuationOf q) (1223)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 2 (meaning1217 q) (meaning1223 q) hs
  change valuationOf q 1217 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 1217 = false ∨ valuation q 1223 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 1218 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_right (literal (valuationOf q) (1218)) (literal (valuationOf q) (1224)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 3 (meaning1218 q) (meaning1224 q) hs
  change valuationOf q 1218 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 1218 = false ∨ valuation q 1224 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 1219 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_right (literal (valuationOf q) (1219)) (literal (valuationOf q) (1225)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 4 (meaning1219 q) (meaning1225 q) hs
  change valuationOf q 1219 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 1219 = false ∨ valuation q 1225 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1223)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 1 1 (meaning1200 q) (meaning1216 q) (meaning1223 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1216 = false ∨ valuation q 1223 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1224)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 1 2 (meaning1200 q) (meaning1217 q) (meaning1224 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1217 = false ∨ valuation q 1224 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1225)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 1 3 (meaning1200 q) (meaning1218 q) (meaning1225 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1218 = false ∨ valuation q 1225 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1226 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1219)) (literal (valuationOf q) (1226)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 1 4 (meaning1200 q) (meaning1219 q) (meaning1226 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1219 = false ∨ valuation q 1226 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1224)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 2 1 (meaning1201 q) (meaning1216 q) (meaning1224 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1216 = false ∨ valuation q 1224 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1225)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 2 2 (meaning1201 q) (meaning1217 q) (meaning1225 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1217 = false ∨ valuation q 1225 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1226 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1226)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 2 3 (meaning1201 q) (meaning1218 q) (meaning1226 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1218 = false ∨ valuation q 1226 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1225)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 3 1 (meaning1202 q) (meaning1216 q) (meaning1225 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1216 = false ∨ valuation q 1225 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1226 = true := by
  have hs : count1222 q = (countLit q [-1, -2, -5, -9, -10, -13]) + (countLit q [-14, -16, -19, -20, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -9, -10, -13]) (l₂ := [-14, -16, -19, -20, -22, -25])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1226)) (countLit q [-1, -2, -5, -9, -10, -13]) (countLit q [-14, -16, -19, -20, -22, -25]) (count1222 q) 3 2 (meaning1202 q) (meaning1217 q) (meaning1226 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1217 = false ∨ valuation q 1226 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1233 = true := by
  have hs : count1233 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1233)) (countLit q [-29]) (countLit q [-30]) (count1233 q) 1 (meaningNeg29 q) (meaning1233 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1233 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1234 = true := by
  have hs : count1233 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1234)) (countLit q [-29]) (countLit q [-30]) (count1233 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning1234 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 1234 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 1233 = false ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1233)) (literal (valuationOf q) (1235)) (countLit q [-27]) (countLit q [-29, -30]) (count1235 q) 1 (meaning1233 q) (meaning1235 q) hs
  change valuationOf q 1233 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 1233 = false ∨ valuation q 1235 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 1234 = false ∨ valuationOf q 1236 = true := by
  have hs : count1235 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (1234)) (literal (valuationOf q) (1236)) (countLit q [-27]) (countLit q [-29, -30]) (count1235 q) 2 (meaning1234 q) (meaning1236 q) hs
  change valuationOf q 1234 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 1234 = false ∨ valuation q 1236 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1235 = true := by
  have hs : count1235 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1235)) (countLit q [-27]) (countLit q [-29, -30]) (count1235 q) 1 (meaningNeg27 q) (meaning1235 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1235 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true := by
  have hs : count1235 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1233)) (literal (valuationOf q) (1236)) (countLit q [-27]) (countLit q [-29, -30]) (count1235 q) 1 1 (meaningNeg27 q) (meaning1233 q) (meaning1236 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1233 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1233 = false ∨ valuation q 1236 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1238 = true := by
  have hs : count1238 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1238)) (countLit q [-34]) (countLit q [-36]) (count1238 q) 1 (meaningNeg36 q) (meaning1238 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1238 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1238 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E234.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112234
