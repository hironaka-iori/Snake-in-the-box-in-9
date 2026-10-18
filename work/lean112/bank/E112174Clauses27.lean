import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1281 = false ∨ valuationOf q 1285 = true := by
  have hs : count1284 q = (countLit q [-44, -46]) + (countLit q [-47, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-47, -49])
  have hm := merge_left (literal (valuationOf q) (1281)) (literal (valuationOf q) (1285)) (countLit q [-44, -46]) (countLit q [-47, -49]) (count1284 q) 2 (meaning1281 q) (meaning1285 q) hs
  change valuationOf q 1281 = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1281 = false ∨ valuation q 1285 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1284 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_right (literal (valuationOf q) (1284)) (literal (valuationOf q) (1288)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 1 (meaning1284 q) (meaning1288 q) hs
  change valuationOf q 1284 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1284 = false ∨ valuation q 1288 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_right (literal (valuationOf q) (1285)) (literal (valuationOf q) (1289)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 2 (meaning1285 q) (meaning1289 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1289 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_left (literal (valuationOf q) (1277)) (literal (valuationOf q) (1288)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 1 (meaning1277 q) (meaning1288 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1288 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1284)) (literal (valuationOf q) (1289)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 1 1 (meaning1277 q) (meaning1284 q) (meaning1289 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1284 = false ∨ valuation q 1289 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1277)) (literal (valuationOf q) (1285)) (literal (valuationOf q) (1290)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 1 2 (meaning1277 q) (meaning1285 q) (meaning1290 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1285 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1285 = false ∨ valuation q 1290 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_left (literal (valuationOf q) (1278)) (literal (valuationOf q) (1289)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 2 (meaning1278 q) (meaning1289 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1289 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1278 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-39, -40, -42]) + (countLit q [-44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -42]) (l₂ := [-44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1278)) (literal (valuationOf q) (1284)) (literal (valuationOf q) (1290)) (countLit q [-39, -40, -42]) (countLit q [-44, -46, -47, -49]) (count1288 q) 2 1 (meaning1278 q) (meaning1284 q) (meaning1290 q) hs
  change valuationOf q 1278 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1278 = false ∨ valuation q 1284 = false ∨ valuation q 1290 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_right (literal (valuationOf q) (1288)) (literal (valuationOf q) (1295)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 1 (meaning1288 q) (meaning1295 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1295 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_left (literal (valuationOf q) (1269)) (literal (valuationOf q) (1295)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 1 (meaning1269 q) (meaning1295 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1295 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1296)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 1 1 (meaning1269 q) (meaning1288 q) (meaning1296 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1288 = false ∨ valuation q 1296 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1269 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1297 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1269)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1297)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 1 2 (meaning1269 q) (meaning1289 q) (meaning1297 q) hs
  change valuationOf q 1269 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1269 = false ∨ valuation q 1289 = false ∨ valuation q 1297 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_left (literal (valuationOf q) (1270)) (literal (valuationOf q) (1296)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 2 (meaning1270 q) (meaning1296 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1296 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1297 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1297)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 2 1 (meaning1270 q) (meaning1288 q) (meaning1297 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1288 = false ∨ valuation q 1297 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1298 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1298)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 2 2 (meaning1270 q) (meaning1289 q) (meaning1298 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1289 = false ∨ valuation q 1298 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1299 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1290)) (literal (valuationOf q) (1299)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 2 3 (meaning1270 q) (meaning1290 q) (meaning1299 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1290 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1290 = false ∨ valuation q 1299 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1298 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1298)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 3 1 (meaning1271 q) (meaning1288 q) (meaning1298 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1288 = false ∨ valuation q 1298 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1299 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1299)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 3 2 (meaning1271 q) (meaning1289 q) (meaning1299 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1289 = false ∨ valuation q 1299 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1299 = true := by
  have hs : count1295 q = (countLit q [-26, -29, -30, -32, -35, -37]) + (countLit q [-39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-26, -29, -30, -32, -35, -37]) (l₂ := [-39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1299)) (countLit q [-26, -29, -30, -32, -35, -37]) (countLit q [-39, -40, -42, -44, -46, -47, -49]) (count1295 q) 4 1 (meaning1272 q) (meaning1288 q) (meaning1299 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1288 = false ∨ valuation q 1299 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1312 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1312)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 3 2 (meaning1248 q) (meaning1296 q) (meaning1312 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1296 = false ∨ valuation q 1312 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1313 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1248)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1313)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 3 3 (meaning1248 q) (meaning1297 q) (meaning1313 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1297 = false ∨ valuation q 1313 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1313 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1313)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 4 2 (meaning1249 q) (meaning1296 q) (meaning1313 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1296 = false ∨ valuation q 1313 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1314 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1314)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 4 3 (meaning1249 q) (meaning1297 q) (meaning1314 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1297 = false ∨ valuation q 1314 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1315 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1315)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 4 4 (meaning1249 q) (meaning1298 q) (meaning1315 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1298 = false ∨ valuation q 1315 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1316 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1249)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1316)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 4 5 (meaning1249 q) (meaning1299 q) (meaning1316 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1299 = false ∨ valuation q 1316 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1314 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1314)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 5 2 (meaning1250 q) (meaning1296 q) (meaning1314 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1296 = false ∨ valuation q 1314 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1315 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1315)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 5 3 (meaning1250 q) (meaning1297 q) (meaning1315 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1297 = false ∨ valuation q 1315 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1316 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1250)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1316)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 5 4 (meaning1250 q) (meaning1298 q) (meaning1316 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1298 = false ∨ valuation q 1316 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1314 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1314)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 6 1 (meaning1251 q) (meaning1295 q) (meaning1314 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1295 = false ∨ valuation q 1314 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1315 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1315)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 6 2 (meaning1251 q) (meaning1296 q) (meaning1315 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1296 = false ∨ valuation q 1315 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1316 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1297)) (literal (valuationOf q) (1316)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 6 3 (meaning1251 q) (meaning1297 q) (meaning1316 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1297 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1297 = false ∨ valuation q 1316 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1317 = true := by
  have hs : count1308 q = (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) + (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (l₂ := [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1298)) (literal (valuationOf q) (1317)) (countLit q [-1, -2, -5, -7, -8, -9, -11, -13, -15, -19, -20, -23, -24]) (countLit q [-26, -29, -30, -32, -35, -37, -39, -40, -42, -44, -46, -47, -49]) (count1308 q) 6 4 (meaning1251 q) (meaning1298 q) (meaning1317 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1298 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1298 = false ∨ valuation q 1317 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E174.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112174
