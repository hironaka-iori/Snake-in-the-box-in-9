import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1341)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 2 3 (meaning1312 q) (meaning1332 q) (meaning1341 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1332 = false ∨ valuation q 1341 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1342 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1333)) (literal (valuationOf q) (1342)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 2 4 (meaning1312 q) (meaning1333 q) (meaning1342 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1333 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1333 = false ∨ valuation q 1342 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1340 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1340)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 3 1 (meaning1313 q) (meaning1330 q) (meaning1340 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1330 = false ∨ valuation q 1340 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1341)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 3 2 (meaning1313 q) (meaning1331 q) (meaning1341 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1331 = false ∨ valuation q 1341 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1342 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1313)) (literal (valuationOf q) (1332)) (literal (valuationOf q) (1342)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 3 3 (meaning1313 q) (meaning1332 q) (meaning1342 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1332 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1332 = false ∨ valuation q 1342 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1341 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1314)) (literal (valuationOf q) (1330)) (literal (valuationOf q) (1341)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 4 1 (meaning1314 q) (meaning1330 q) (meaning1341 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1330 = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1330 = false ∨ valuation q 1341 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1314 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1342 = true := by
  have hs : count1337 q = (countLit q [-27, -29, -30, -32, -35, -37]) + (countLit q [-40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -35, -37]) (l₂ := [-40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1314)) (literal (valuationOf q) (1331)) (literal (valuationOf q) (1342)) (countLit q [-27, -29, -30, -32, -35, -37]) (countLit q [-40, -41, -42, -44, -45, -48, -49]) (count1337 q) 4 2 (meaning1314 q) (meaning1331 q) (meaning1342 q) hs
  change valuationOf q 1314 = false ∨ valuationOf q 1331 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1314 = false ∨ valuation q 1331 = false ∨ valuation q 1342 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1354)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 1 4 (meaning1288 q) (meaning1340 q) (meaning1354 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1340 = false ∨ valuation q 1354 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 1 5 (meaning1288 q) (meaning1341 q) (meaning1355 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1341 = false ∨ valuation q 1355 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1352 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1352)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 2 1 (meaning1289 q) (meaning1337 q) (meaning1352 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1337 = false ∨ valuation q 1352 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1353 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1353)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 2 2 (meaning1289 q) (meaning1338 q) (meaning1353 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1338 = false ∨ valuation q 1353 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1354)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 2 3 (meaning1289 q) (meaning1339 q) (meaning1354 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1339 = false ∨ valuation q 1354 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 2 4 (meaning1289 q) (meaning1340 q) (meaning1355 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1340 = false ∨ valuation q 1355 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1356)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 2 5 (meaning1289 q) (meaning1341 q) (meaning1356 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1341 = false ∨ valuation q 1356 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1289 = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1357 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1289)) (literal (valuationOf q) (1342)) (literal (valuationOf q) (1357)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 2 6 (meaning1289 q) (meaning1342 q) (meaning1357 q) hs
  change valuationOf q 1289 = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1289 = false ∨ valuation q 1342 = false ∨ valuation q 1357 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1353 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1353)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 3 1 (meaning1290 q) (meaning1337 q) (meaning1353 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1337 = false ∨ valuation q 1353 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1354)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 3 2 (meaning1290 q) (meaning1338 q) (meaning1354 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1338 = false ∨ valuation q 1354 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 3 3 (meaning1290 q) (meaning1339 q) (meaning1355 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1339 = false ∨ valuation q 1355 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1356)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 3 4 (meaning1290 q) (meaning1340 q) (meaning1356 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1340 = false ∨ valuation q 1356 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1357 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1290)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1357)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 3 5 (meaning1290 q) (meaning1341 q) (meaning1357 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1341 = false ∨ valuation q 1357 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1353 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_left (literal (valuationOf q) (1291)) (literal (valuationOf q) (1353)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 (meaning1291 q) (meaning1353 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1353 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1354 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1354)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 1 (meaning1291 q) (meaning1337 q) (meaning1354 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1337 = false ∨ valuation q 1354 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 2 (meaning1291 q) (meaning1338 q) (meaning1355 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1338 = false ∨ valuation q 1355 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1356)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 3 (meaning1291 q) (meaning1339 q) (meaning1356 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1339 = false ∨ valuation q 1356 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1357 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1357)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 4 (meaning1291 q) (meaning1340 q) (meaning1357 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1340 = false ∨ valuation q 1357 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1358 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1358)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 5 (meaning1291 q) (meaning1341 q) (meaning1358 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1341 = false ∨ valuation q 1358 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1359 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1342)) (literal (valuationOf q) (1359)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 4 6 (meaning1291 q) (meaning1342 q) (meaning1359 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1342 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1342 = false ∨ valuation q 1359 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1355 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1337)) (literal (valuationOf q) (1355)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 5 1 (meaning1292 q) (meaning1337 q) (meaning1355 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1337 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1337 = false ∨ valuation q 1355 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1356 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1338)) (literal (valuationOf q) (1356)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 5 2 (meaning1292 q) (meaning1338 q) (meaning1356 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1338 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1338 = false ∨ valuation q 1356 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1357 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1339)) (literal (valuationOf q) (1357)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 5 3 (meaning1292 q) (meaning1339 q) (meaning1357 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1339 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1339 = false ∨ valuation q 1357 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1358 = true := by
  have hs : count1350 q = (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) + (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (l₂ := [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49])
  have hm := merge_two (literal (valuationOf q) (1292)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1358)) (countLit q [-2, -4, -7, -8, -9, -10, -11, -14, -15, -18, -20, -23, -25]) (countLit q [-27, -29, -30, -32, -35, -37, -40, -41, -42, -44, -45, -48, -49]) (count1350 q) 5 4 (meaning1292 q) (meaning1340 q) (meaning1358 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1340 = false ∨ valuation q 1358 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1363 = true := by
  have hs : count1363 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1363)) (countLit q [-53]) (countLit q [-55]) (count1363 q) 1 (meaningNeg55 q) (meaning1363 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1363 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E091.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112091
