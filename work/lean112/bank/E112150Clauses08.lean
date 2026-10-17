import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1335 = true := by
  have hs : count1334 q = (countLit q [-46, -49]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1335)) (countLit q [-46, -49]) (countLit q [-51, -53]) (count1334 q) 1 1 (meaning1330 q) (meaning1332 q) (meaning1335 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1332 = false ∨ valuation q 1335 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_right (literal (valuationOf q) (1334)) (literal (valuationOf q) (1338)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 1 (meaning1334 q) (meaning1338 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1338 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_right (literal (valuationOf q) (1335)) (literal (valuationOf q) (1339)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 2 (meaning1335 q) (meaning1339 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1339 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1338 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_left (literal (valuationOf q) (1327)) (literal (valuationOf q) (1338)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 1 (meaning1327 q) (meaning1338 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1338 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1339)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 1 1 (meaning1327 q) (meaning1334 q) (meaning1339 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1334 = false ∨ valuation q 1339 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1340 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1335)) (literal (valuationOf q) (1340)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 1 2 (meaning1327 q) (meaning1335 q) (meaning1340 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1335 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1335 = false ∨ valuation q 1340 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1339 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_left (literal (valuationOf q) (1328)) (literal (valuationOf q) (1339)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 2 (meaning1328 q) (meaning1339 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1339 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1340 = true := by
  have hs : count1338 q = (countLit q [-40, -42, -44]) + (countLit q [-46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-40, -42, -44]) (l₂ := [-46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1334)) (literal (valuationOf q) (1340)) (countLit q [-40, -42, -44]) (countLit q [-46, -49, -51, -53]) (count1338 q) 2 1 (meaning1328 q) (meaning1334 q) (meaning1340 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1334 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1334 = false ∨ valuation q 1340 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1346)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 1 1 (meaning1319 q) (meaning1338 q) (meaning1346 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1338 = false ∨ valuation q 1346 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1347 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1347)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 1 2 (meaning1319 q) (meaning1339 q) (meaning1347 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1339 = false ∨ valuation q 1347 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 1319 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1348 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1319)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1348)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 1 3 (meaning1319 q) (meaning1340 q) (meaning1348 q) hs
  change valuationOf q 1319 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 1319 = false ∨ valuation q 1340 = false ∨ valuation q 1348 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1347 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1347)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 2 1 (meaning1320 q) (meaning1338 q) (meaning1347 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1338 = false ∨ valuation q 1347 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1348 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1348)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 2 2 (meaning1320 q) (meaning1339 q) (meaning1348 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1339 = false ∨ valuation q 1348 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1349 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1320)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1349)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 2 3 (meaning1320 q) (meaning1340 q) (meaning1349 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1340 = false ∨ valuation q 1349 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1348 = true := by
  have hs : count1345 q = (countLit q [-28, -30, -33, -35, -37, -38]) + (countLit q [-40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -33, -35, -37, -38]) (l₂ := [-40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1321)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1348)) (countLit q [-28, -30, -33, -35, -37, -38]) (countLit q [-40, -42, -44, -46, -49, -51, -53]) (count1345 q) 3 1 (meaning1321 q) (meaning1338 q) (meaning1348 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1338 = false ∨ valuation q 1348 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1361 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1298)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1361)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 2 3 (meaning1298 q) (meaning1347 q) (meaning1361 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1347 = false ∨ valuation q 1361 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1362 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1298)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1362)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 2 4 (meaning1298 q) (meaning1348 q) (meaning1362 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1348 = false ∨ valuation q 1362 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1298 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1363 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1298)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1363)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 2 5 (meaning1298 q) (meaning1349 q) (meaning1363 q) hs
  change valuationOf q 1298 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1298 = false ∨ valuation q 1349 = false ∨ valuation q 1363 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1361 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1299)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1361)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 3 2 (meaning1299 q) (meaning1346 q) (meaning1361 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1346 = false ∨ valuation q 1361 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1362 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1299)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1362)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 3 3 (meaning1299 q) (meaning1347 q) (meaning1362 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1347 = false ∨ valuation q 1362 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1299 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1363 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1299)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1363)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 3 4 (meaning1299 q) (meaning1348 q) (meaning1363 q) hs
  change valuationOf q 1299 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1299 = false ∨ valuation q 1348 = false ∨ valuation q 1363 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1300 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1362 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1300)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1362)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 4 2 (meaning1300 q) (meaning1346 q) (meaning1362 q) hs
  change valuationOf q 1300 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1300 = false ∨ valuation q 1346 = false ∨ valuation q 1362 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1363 = true := by
  have hs : count1357 q = (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) + (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (l₂ := [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1346)) (literal (valuationOf q) (1363)) (countLit q [-2, -3, -5, -7, -11, -12, -14, -17, -19, -21, -22, -24, -26]) (countLit q [-28, -30, -33, -35, -37, -38, -40, -42, -44, -46, -49, -51, -53]) (count1357 q) 5 2 (meaning1301 q) (meaning1346 q) (meaning1363 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1346 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1346 = false ∨ valuation q 1363 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1369)) (countLit q [-56]) (countLit q [-58]) (count1369 q) 1 (meaningNeg58 q) (meaning1369 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1369 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1369 = true := by
  have hs : count1369 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1369)) (countLit q [-56]) (countLit q [-58]) (count1369 q) 1 (meaningNeg56 q) (meaning1369 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1369 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1369 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1369 = false ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1369)) (literal (valuationOf q) (1371)) (countLit q [-54]) (countLit q [-56, -58]) (count1371 q) 1 (meaning1369 q) (meaning1371 q) hs
  change valuationOf q 1369 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1369 = false ∨ valuation q 1371 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1371 = true := by
  have hs : count1371 q = (countLit q [-54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1371)) (countLit q [-54]) (countLit q [-56, -58]) (count1371 q) 1 (meaningNeg54 q) (meaning1371 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1371 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-54, -56, -58]) + (countLit q [-61, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-61, -64, -66])
  have hm := merge_left (literal (valuationOf q) (1371)) (literal (valuationOf q) (1379)) (countLit q [-54, -56, -58]) (countLit q [-61, -64, -66]) (count1379 q) 1 (meaning1371 q) (meaning1379 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1379 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1386 = true := by
  have hs : count1385 q = (countLit q [-68]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1386)) (countLit q [-68]) (countLit q [-70]) (count1385 q) 1 1 (meaningNeg68 q) (meaningNeg70 q) (meaning1386 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 70 = true ∨ valuation q 1386 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1387 = true := by
  have hs : count1387 q = (countLit q [-67]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68, -70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1387)) (countLit q [-67]) (countLit q [-68, -70]) (count1387 q) 1 (meaningNeg67 q) (meaning1387 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1387 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1387 q = (countLit q [-67]) + (countLit q [-68, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68, -70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-67]) (countLit q [-68, -70]) (count1387 q) 1 2 (meaningNeg67 q) (meaning1386 q) (meaning1389 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1390 = true := by
  have hs : count1390 q = (countLit q [-72]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1390)) (countLit q [-72]) (countLit q [-75]) (count1390 q) 1 (meaningNeg75 q) (meaning1390 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1390 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E150.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112150
