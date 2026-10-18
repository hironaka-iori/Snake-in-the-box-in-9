import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1208)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1217)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 1 1 (meaning1208 q) (meaning1213 q) (meaning1217 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1213 = false ∨ valuation q 1217 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 1208 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1218 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1208)) (literal (valuationOf q) (1214)) (literal (valuationOf q) (1218)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 1 2 (meaning1208 q) (meaning1214 q) (meaning1218 q) hs
  change valuationOf q 1208 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 1208 = false ∨ valuation q 1214 = false ∨ valuation q 1218 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1217 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_left (literal (valuationOf q) (1209)) (literal (valuationOf q) (1217)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 2 (meaning1209 q) (meaning1217 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1217 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1218 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1209)) (literal (valuationOf q) (1213)) (literal (valuationOf q) (1218)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 2 1 (meaning1209 q) (meaning1213 q) (meaning1218 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1213 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1213 = false ∨ valuation q 1218 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 1209 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1219 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1209)) (literal (valuationOf q) (1214)) (literal (valuationOf q) (1219)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 2 2 (meaning1209 q) (meaning1214 q) (meaning1219 q) hs
  change valuationOf q 1209 = false ∨ valuationOf q 1214 = false ∨ valuationOf q 1219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 1209 = false ∨ valuation q 1214 = false ∨ valuation q 1219 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 1210 = false ∨ valuationOf q 1218 = true := by
  have hs : count1216 q = (countLit q [-38, -41, -43]) + (countLit q [-44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-44, -45, -48])
  have hm := merge_left (literal (valuationOf q) (1210)) (literal (valuationOf q) (1218)) (countLit q [-38, -41, -43]) (countLit q [-44, -45, -48]) (count1216 q) 3 (meaning1210 q) (meaning1218 q) hs
  change valuationOf q 1210 = false ∨ valuationOf q 1218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 1210 = false ∨ valuation q 1218 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1222 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_left (literal (valuationOf q) (1200)) (literal (valuationOf q) (1222)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 1 (meaning1200 q) (meaning1222 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1222 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1223)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 1 1 (meaning1200 q) (meaning1216 q) (meaning1223 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1216 = false ∨ valuation q 1223 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1224)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 1 2 (meaning1200 q) (meaning1217 q) (meaning1224 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1217 = false ∨ valuation q 1224 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1218)) (literal (valuationOf q) (1225)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 1 3 (meaning1200 q) (meaning1218 q) (meaning1225 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1218 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1218 = false ∨ valuation q 1225 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1200 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1226 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1200)) (literal (valuationOf q) (1219)) (literal (valuationOf q) (1226)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 1 4 (meaning1200 q) (meaning1219 q) (meaning1226 q) hs
  change valuationOf q 1200 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1200 = false ∨ valuation q 1219 = false ∨ valuation q 1226 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1223 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_left (literal (valuationOf q) (1201)) (literal (valuationOf q) (1223)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 2 (meaning1201 q) (meaning1223 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1223 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1224)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 2 1 (meaning1201 q) (meaning1216 q) (meaning1224 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1216 = false ∨ valuation q 1224 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1225)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 2 2 (meaning1201 q) (meaning1217 q) (meaning1225 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1217 = false ∨ valuation q 1225 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1201 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1227 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1201)) (literal (valuationOf q) (1219)) (literal (valuationOf q) (1227)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 2 4 (meaning1201 q) (meaning1219 q) (meaning1227 q) hs
  change valuationOf q 1201 = false ∨ valuationOf q 1219 = false ∨ valuationOf q 1227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1201 = false ∨ valuation q 1219 = false ∨ valuation q 1227 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1224 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_left (literal (valuationOf q) (1202)) (literal (valuationOf q) (1224)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 3 (meaning1202 q) (meaning1224 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1224 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1225 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1216)) (literal (valuationOf q) (1225)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 3 1 (meaning1202 q) (meaning1216 q) (meaning1225 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1216 = false ∨ valuationOf q 1225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1216 = false ∨ valuation q 1225 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1226 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1226)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 3 2 (meaning1202 q) (meaning1217 q) (meaning1226 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1217 = false ∨ valuation q 1226 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1203 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1227 = true := by
  have hs : count1222 q = (countLit q [-26, -27, -29, -32, -33, -35]) + (countLit q [-38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -29, -32, -33, -35]) (l₂ := [-38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1203)) (literal (valuationOf q) (1217)) (literal (valuationOf q) (1227)) (countLit q [-26, -27, -29, -32, -33, -35]) (countLit q [-38, -41, -43, -44, -45, -48]) (count1222 q) 4 2 (meaning1203 q) (meaning1217 q) (meaning1227 q) hs
  change valuationOf q 1203 = false ∨ valuationOf q 1217 = false ∨ valuationOf q 1227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1203 = false ∨ valuation q 1217 = false ∨ valuation q 1227 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1181 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1233 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1181)) (literal (valuationOf q) (1223)) (literal (valuationOf q) (1233)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 1 2 (meaning1181 q) (meaning1223 q) (meaning1233 q) hs
  change valuationOf q 1181 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1181 = false ∨ valuation q 1223 = false ∨ valuation q 1233 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1181 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1234 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1181)) (literal (valuationOf q) (1224)) (literal (valuationOf q) (1234)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 1 3 (meaning1181 q) (meaning1224 q) (meaning1234 q) hs
  change valuationOf q 1181 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1181 = false ∨ valuation q 1224 = false ∨ valuation q 1234 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1181 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1235 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1181)) (literal (valuationOf q) (1225)) (literal (valuationOf q) (1235)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 1 4 (meaning1181 q) (meaning1225 q) (meaning1235 q) hs
  change valuationOf q 1181 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1181 = false ∨ valuation q 1225 = false ∨ valuation q 1235 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1181 = false ∨ valuationOf q 1226 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1181)) (literal (valuationOf q) (1226)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 1 5 (meaning1181 q) (meaning1226 q) (meaning1236 q) hs
  change valuationOf q 1181 = false ∨ valuationOf q 1226 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1181 = false ∨ valuation q 1226 = false ∨ valuation q 1236 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1181 = false ∨ valuationOf q 1227 = false ∨ valuationOf q 1237 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1181)) (literal (valuationOf q) (1227)) (literal (valuationOf q) (1237)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 1 6 (meaning1181 q) (meaning1227 q) (meaning1237 q) hs
  change valuationOf q 1181 = false ∨ valuationOf q 1227 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1181 = false ∨ valuation q 1227 = false ∨ valuation q 1237 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1222 = false ∨ valuationOf q 1233 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1182)) (literal (valuationOf q) (1222)) (literal (valuationOf q) (1233)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 2 1 (meaning1182 q) (meaning1222 q) (meaning1233 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1222 = false ∨ valuationOf q 1233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1222 = false ∨ valuation q 1233 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1234 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1182)) (literal (valuationOf q) (1223)) (literal (valuationOf q) (1234)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 2 2 (meaning1182 q) (meaning1223 q) (meaning1234 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1234 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1223 = false ∨ valuation q 1234 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1235 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1182)) (literal (valuationOf q) (1224)) (literal (valuationOf q) (1235)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 2 3 (meaning1182 q) (meaning1224 q) (meaning1235 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1224 = false ∨ valuation q 1235 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1182)) (literal (valuationOf q) (1225)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 2 4 (meaning1182 q) (meaning1225 q) (meaning1236 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1225 = false ∨ valuation q 1236 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1182 = false ∨ valuationOf q 1226 = false ∨ valuationOf q 1237 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1182)) (literal (valuationOf q) (1226)) (literal (valuationOf q) (1237)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 2 5 (meaning1182 q) (meaning1226 q) (meaning1237 q) hs
  change valuationOf q 1182 = false ∨ valuationOf q 1226 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1182 = false ∨ valuation q 1226 = false ∨ valuation q 1237 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1183 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1235 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1183)) (literal (valuationOf q) (1223)) (literal (valuationOf q) (1235)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 3 2 (meaning1183 q) (meaning1223 q) (meaning1235 q) hs
  change valuationOf q 1183 = false ∨ valuationOf q 1223 = false ∨ valuationOf q 1235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1183 = false ∨ valuation q 1223 = false ∨ valuation q 1235 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1183 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1236 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1183)) (literal (valuationOf q) (1224)) (literal (valuationOf q) (1236)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 3 3 (meaning1183 q) (meaning1224 q) (meaning1236 q) hs
  change valuationOf q 1183 = false ∨ valuationOf q 1224 = false ∨ valuationOf q 1236 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1183 = false ∨ valuation q 1224 = false ∨ valuation q 1236 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1183 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1237 = true := by
  have hs : count1231 q = (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) + (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (l₂ := [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48])
  have hm := merge_two (literal (valuationOf q) (1183)) (literal (valuationOf q) (1225)) (literal (valuationOf q) (1237)) (countLit q [-2, -3, -5, -8, -10, -11, -14, -16, -17, -19, -22, -23]) (countLit q [-26, -27, -29, -32, -33, -35, -38, -41, -43, -44, -45, -48]) (count1231 q) 3 4 (meaning1183 q) (meaning1225 q) (meaning1237 q) hs
  change valuationOf q 1183 = false ∨ valuationOf q 1225 = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1183 = false ∨ valuation q 1225 = false ∨ valuation q 1237 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E170.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112170
