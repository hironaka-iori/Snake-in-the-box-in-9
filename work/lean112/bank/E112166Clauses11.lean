import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1328)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 1 1 (meaning1301 q) (meaning1320 q) (meaning1328 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1320 = false ∨ valuation q 1328 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1329)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 1 2 (meaning1301 q) (meaning1321 q) (meaning1329 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1321 = false ∨ valuation q 1329 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1330)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 1 3 (meaning1301 q) (meaning1322 q) (meaning1330 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1322 = false ∨ valuation q 1330 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1302)) (literal (valuationOf q) (1328)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 2 (meaning1302 q) (meaning1328 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1328 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1329)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 2 1 (meaning1302 q) (meaning1320 q) (meaning1329 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1320 = false ∨ valuation q 1329 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1330)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 2 2 (meaning1302 q) (meaning1321 q) (meaning1330 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1321 = false ∨ valuation q 1330 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1331 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1331)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 2 3 (meaning1302 q) (meaning1322 q) (meaning1331 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1322 = false ∨ valuation q 1331 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1303)) (literal (valuationOf q) (1329)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 3 (meaning1303 q) (meaning1329 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1329 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1330)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 3 1 (meaning1303 q) (meaning1320 q) (meaning1330 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1320 = false ∨ valuation q 1330 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1331 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1331)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 3 2 (meaning1303 q) (meaning1321 q) (meaning1331 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1321 = false ∨ valuation q 1331 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_left (literal (valuationOf q) (1304)) (literal (valuationOf q) (1330)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 4 (meaning1304 q) (meaning1330 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1330 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1331)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 4 1 (meaning1304 q) (meaning1320 q) (meaning1331 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1320 = false ∨ valuation q 1331 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1332 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1332)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 4 2 (meaning1304 q) (meaning1321 q) (meaning1332 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1321 = false ∨ valuation q 1332 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 1304 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true := by
  have hs : count1327 q = (countLit q [-2, -3, -5, -7, -8, -11]) + (countLit q [-13, -14, -17, -19, -21, -22, -24]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11]) (l₂ := [-13, -14, -17, -19, -21, -22, -24])
  have hm := merge_two (literal (valuationOf q) (1304)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1333)) (countLit q [-2, -3, -5, -7, -8, -11]) (countLit q [-13, -14, -17, -19, -21, -22, -24]) (count1327 q) 4 3 (meaning1304 q) (meaning1322 q) (meaning1333 q) hs
  change valuationOf q 1304 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 1304 = false ∨ valuation q 1322 = false ∨ valuation q 1333 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1340)) (countLit q [-28]) (countLit q [-29]) (count1340 q) 1 (meaningNeg29 q) (meaning1340 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1340 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1340)) (countLit q [-28]) (countLit q [-29]) (count1340 q) 1 (meaningNeg28 q) (meaning1340 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1340 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28, -29])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1342)) (countLit q [-25]) (countLit q [-28, -29]) (count1342 q) 1 (meaning1340 q) (meaning1342 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1342 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28, -29])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1342)) (countLit q [-25]) (countLit q [-28, -29]) (count1342 q) 1 (meaningNeg25 q) (meaning1342 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1342 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1342 q = (countLit q [-25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-25]) (countLit q [-28, -29]) (count1342 q) 1 1 (meaningNeg25 q) (meaning1340 q) (meaning1343 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1340 = false ∨ valuation q 1343 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1345)) (countLit q [-32]) (countLit q [-34]) (count1345 q) 1 (meaningNeg34 q) (meaning1345 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1345 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1345)) (countLit q [-32]) (countLit q [-34]) (count1345 q) 1 (meaningNeg32 q) (meaning1345 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1345 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1347)) (countLit q [-36]) (countLit q [-37]) (count1347 q) 1 (meaningNeg37 q) (meaning1347 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1347 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1347 = true := by
  have hs : count1347 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1347)) (countLit q [-36]) (countLit q [-37]) (count1347 q) 1 (meaningNeg36 q) (meaning1347 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1347 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-32, -34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-36, -37])
  have hm := merge_right (literal (valuationOf q) (1347)) (literal (valuationOf q) (1349)) (countLit q [-32, -34]) (countLit q [-36, -37]) (count1349 q) 1 (meaning1347 q) (meaning1349 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1349 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-32, -34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-36, -37])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1349)) (countLit q [-32, -34]) (countLit q [-36, -37]) (count1349 q) 1 (meaning1345 q) (meaning1349 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1349 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-32, -34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-36, -37])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1347)) (literal (valuationOf q) (1350)) (countLit q [-32, -34]) (countLit q [-36, -37]) (count1349 q) 1 1 (meaning1345 q) (meaning1347 q) (meaning1350 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1347 = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1347 = false ∨ valuation q 1350 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1353 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1353)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 1 (meaning1349 q) (meaning1353 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1353 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1354)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 2 (meaning1350 q) (meaning1354 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1354 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1353 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_left (literal (valuationOf q) (1342)) (literal (valuationOf q) (1353)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 1 (meaning1342 q) (meaning1353 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1353 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1354)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 1 1 (meaning1342 q) (meaning1349 q) (meaning1354 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1349 = false ∨ valuation q 1354 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1355)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 1 2 (meaning1342 q) (meaning1350 q) (meaning1355 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1350 = false ∨ valuation q 1355 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1354 = true := by
  have hs : count1353 q = (countLit q [-25, -28, -29]) + (countLit q [-32, -34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-25, -28, -29]) (l₂ := [-32, -34, -36, -37])
  have hm := merge_left (literal (valuationOf q) (1343)) (literal (valuationOf q) (1354)) (countLit q [-25, -28, -29]) (countLit q [-32, -34, -36, -37]) (count1353 q) 2 (meaning1343 q) (meaning1354 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1354 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E166.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112166
