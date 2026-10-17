import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 1196 = false ∨ valuationOf q 1198 = true := by
  have hs : count1197 q = (countLit q [-32]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (1196)) (literal (valuationOf q) (1198)) (countLit q [-32]) (countLit q [-33, -35]) (count1197 q) 2 (meaning1196 q) (meaning1198 q) hs
  change valuationOf q 1196 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 1196 = false ∨ valuation q 1198 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1197 = true := by
  have hs : count1197 q = (countLit q [-32]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1197)) (countLit q [-32]) (countLit q [-33, -35]) (count1197 q) 1 (meaningNeg32 q) (meaning1197 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1197 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1197 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1195 = false ∨ valuationOf q 1198 = true := by
  have hs : count1197 q = (countLit q [-32]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1195)) (literal (valuationOf q) (1198)) (countLit q [-32]) (countLit q [-33, -35]) (count1197 q) 1 1 (meaningNeg32 q) (meaning1195 q) (meaning1198 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1195 = false ∨ valuationOf q 1198 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1195 = false ∨ valuation q 1198 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 1197 = false ∨ valuationOf q 1200 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_right (literal (valuationOf q) (1197)) (literal (valuationOf q) (1200)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 1 (meaning1197 q) (meaning1200 q) hs
  change valuationOf q 1197 = false ∨ valuationOf q 1200 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 1197 = false ∨ valuation q 1200 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 1198 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_right (literal (valuationOf q) (1198)) (literal (valuationOf q) (1201)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 2 (meaning1198 q) (meaning1201 q) hs
  change valuationOf q 1198 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 1198 = false ∨ valuation q 1201 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1200 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_left (literal (valuationOf q) (1192)) (literal (valuationOf q) (1200)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 1 (meaning1192 q) (meaning1200 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1200 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1200 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_two (literal (valuationOf q) (1192)) (literal (valuationOf q) (1197)) (literal (valuationOf q) (1201)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 1 1 (meaning1192 q) (meaning1197 q) (meaning1201 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1197 = false ∨ valuation q 1201 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1192 = false ∨ valuationOf q 1198 = false ∨ valuationOf q 1202 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_two (literal (valuationOf q) (1192)) (literal (valuationOf q) (1198)) (literal (valuationOf q) (1202)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 1 2 (meaning1192 q) (meaning1198 q) (meaning1202 q) hs
  change valuationOf q 1192 = false ∨ valuationOf q 1198 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1192 = false ∨ valuation q 1198 = false ∨ valuation q 1202 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1193 = false ∨ valuationOf q 1201 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_left (literal (valuationOf q) (1193)) (literal (valuationOf q) (1201)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 2 (meaning1193 q) (meaning1201 q) hs
  change valuationOf q 1193 = false ∨ valuationOf q 1201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1193 = false ∨ valuation q 1201 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1193 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1202 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_two (literal (valuationOf q) (1193)) (literal (valuationOf q) (1197)) (literal (valuationOf q) (1202)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 2 1 (meaning1193 q) (meaning1197 q) (meaning1202 q) hs
  change valuationOf q 1193 = false ∨ valuationOf q 1197 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1193 = false ∨ valuation q 1197 = false ∨ valuation q 1202 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 1193 = false ∨ valuationOf q 1198 = false ∨ valuationOf q 1203 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_two (literal (valuationOf q) (1193)) (literal (valuationOf q) (1198)) (literal (valuationOf q) (1203)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 2 2 (meaning1193 q) (meaning1198 q) (meaning1203 q) hs
  change valuationOf q 1193 = false ∨ valuationOf q 1198 = false ∨ valuationOf q 1203 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 1193 = false ∨ valuation q 1198 = false ∨ valuation q 1203 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 1194 = false ∨ valuationOf q 1202 = true := by
  have hs : count1200 q = (countLit q [-26, -27, -29]) + (countLit q [-32, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29]) (l₂ := [-32, -33, -35])
  have hm := merge_left (literal (valuationOf q) (1194)) (literal (valuationOf q) (1202)) (countLit q [-26, -27, -29]) (countLit q [-32, -33, -35]) (count1200 q) 3 (meaning1194 q) (meaning1202 q) hs
  change valuationOf q 1194 = false ∨ valuationOf q 1202 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 1194 = false ∨ valuation q 1202 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1206)) (countLit q [-41]) (countLit q [-43]) (count1206 q) 1 (meaningNeg43 q) (meaning1206 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1206 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1206 = true := by
  have hs : count1206 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1206)) (countLit q [-41]) (countLit q [-43]) (count1206 q) 1 (meaningNeg41 q) (meaning1206 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1206 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1206 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1207 = true := by
  have hs : count1206 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1207)) (countLit q [-41]) (countLit q [-43]) (count1206 q) 1 1 (meaningNeg41 q) (meaningNeg43 q) (meaning1207 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1207 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 1207 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 1206 = false ∨ valuationOf q 1208 = true := by
  have hs : count1208 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_right (literal (valuationOf q) (1206)) (literal (valuationOf q) (1208)) (countLit q [-38]) (countLit q [-41, -43]) (count1208 q) 1 (meaning1206 q) (meaning1208 q) hs
  change valuationOf q 1206 = false ∨ valuationOf q 1208 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 1206 = false ∨ valuation q 1208 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 1207 = false ∨ valuationOf q 1209 = true := by
  have hs : count1208 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_right (literal (valuationOf q) (1207)) (literal (valuationOf q) (1209)) (countLit q [-38]) (countLit q [-41, -43]) (count1208 q) 2 (meaning1207 q) (meaning1209 q) hs
  change valuationOf q 1207 = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 1207 = false ∨ valuation q 1209 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1208 = true := by
  have hs : count1208 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1208)) (countLit q [-38]) (countLit q [-41, -43]) (count1208 q) 1 (meaningNeg38 q) (meaning1208 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1208 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1208 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1206 = false ∨ valuationOf q 1209 = true := by
  have hs : count1208 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (1206)) (literal (valuationOf q) (1209)) (countLit q [-38]) (countLit q [-41, -43]) (count1208 q) 1 1 (meaningNeg38 q) (meaning1206 q) (meaning1209 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1206 = false ∨ valuationOf q 1209 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1206 = false ∨ valuation q 1209 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1207 = false ∨ valuationOf q 1210 = true := by
  have hs : count1208 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (1207)) (literal (valuationOf q) (1210)) (countLit q [-38]) (countLit q [-41, -43]) (count1208 q) 1 2 (meaningNeg38 q) (meaning1207 q) (meaning1210 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1207 = false ∨ valuationOf q 1210 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1207 = false ∨ valuation q 1210 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1211 = true := by
  have hs : count1211 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1211)) (countLit q [-45]) (countLit q [-48]) (count1211 q) 1 (meaningNeg48 q) (meaning1211 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1211 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1211 = true := by
  have hs : count1211 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1211)) (countLit q [-45]) (countLit q [-48]) (count1211 q) 1 (meaningNeg45 q) (meaning1211 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1211 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1212 = true := by
  have hs : count1211 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1212)) (countLit q [-45]) (countLit q [-48]) (count1211 q) 1 1 (meaningNeg45 q) (meaningNeg48 q) (meaning1212 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 48 = true ∨ valuation q 1212 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1211 = false ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-44]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45, -48])
  have hm := merge_right (literal (valuationOf q) (1211)) (literal (valuationOf q) (1213)) (countLit q [-44]) (countLit q [-45, -48]) (count1213 q) 1 (meaning1211 q) (meaning1213 q) hs
  change valuationOf q 1211 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1211 = false ∨ valuation q 1213 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1212 = false ∨ valuationOf q 1214 = true := by
  have hs : count1213 q = (countLit q [-44]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45, -48])
  have hm := merge_right (literal (valuationOf q) (1212)) (literal (valuationOf q) (1214)) (countLit q [-44]) (countLit q [-45, -48]) (count1213 q) 2 (meaning1212 q) (meaning1214 q) hs
  change valuationOf q 1212 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1212 = false ∨ valuation q 1214 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1213 = true := by
  have hs : count1213 q = (countLit q [-44]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45, -48])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1213)) (countLit q [-44]) (countLit q [-45, -48]) (count1213 q) 1 (meaningNeg44 q) (meaning1213 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1213 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true := by
  have hs : count1213 q = (countLit q [-44]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45, -48])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (1211)) (literal (valuationOf q) (1214)) (countLit q [-44]) (countLit q [-45, -48]) (count1213 q) 1 1 (meaningNeg44 q) (meaning1211 q) (meaning1214 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1211 = false ∨ valuationOf q 1214 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1211 = false ∨ valuation q 1214 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1212 = false ∨ valuationOf q 1215 = true := by
  have hs : count1213 q = (countLit q [-44]) + (countLit q [-45, -48]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45, -48])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (1212)) (literal (valuationOf q) (1215)) (countLit q [-44]) (countLit q [-45, -48]) (count1213 q) 1 2 (meaningNeg44 q) (meaning1212 q) (meaning1215 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1212 = false ∨ valuationOf q 1215 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1212 = false ∨ valuation q 1215 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1213 = false ∨ valuationOf q 1216 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_right (literal (valuationOf q) (1213)) (literal (valuationOf q) (1216)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 1 (meaning1213 q) (meaning1216 q) hs
  change valuationOf q 1213 = false ∨ valuationOf q 1216 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1213 = false ∨ valuation q 1216 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 1214 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_right (literal (valuationOf q) (1214)) (literal (valuationOf q) (1217)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 2 (meaning1214 q) (meaning1217 q) hs
  change valuationOf q 1214 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 1214 = false ∨ valuation q 1217 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 1215 = false ∨ valuationOf q 1218 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_right (literal (valuationOf q) (1215)) (literal (valuationOf q) (1218)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 3 (meaning1215 q) (meaning1218 q) hs
  change valuationOf q 1215 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 1215 = false ∨ valuation q 1218 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1216 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_left (literal (valuationOf q) (1208)) (literal (valuationOf q) (1216)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 1 (meaning1208 q) (meaning1216 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1216 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1216 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E170.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112170
