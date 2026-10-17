import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1315 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-20, -22]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (1315)) (literal (valuationOf q) (1317)) (countLit q [-20, -22]) (countLit q [-23, -24]) (count1316 q) 2 (meaning1315 q) (meaning1317 q) hs
  change valuationOf q 1315 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1315 = false ∨ valuation q 1317 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-20, -22]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (1312)) (literal (valuationOf q) (1316)) (countLit q [-20, -22]) (countLit q [-23, -24]) (count1316 q) 1 (meaning1312 q) (meaning1316 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1316 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-20, -22]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1317)) (countLit q [-20, -22]) (countLit q [-23, -24]) (count1316 q) 1 1 (meaning1312 q) (meaning1314 q) (meaning1317 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1314 = false ∨ valuation q 1317 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1318 = true := by
  have hs : count1316 q = (countLit q [-20, -22]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1315)) (literal (valuationOf q) (1318)) (countLit q [-20, -22]) (countLit q [-23, -24]) (count1316 q) 1 2 (meaning1312 q) (meaning1315 q) (meaning1318 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1315 = false ∨ valuationOf q 1318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1315 = false ∨ valuation q 1318 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1313 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-20, -22]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-20, -22]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (1313)) (literal (valuationOf q) (1317)) (countLit q [-20, -22]) (countLit q [-23, -24]) (count1316 q) 2 (meaning1313 q) (meaning1317 q) hs
  change valuationOf q 1313 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1313 = false ∨ valuation q 1317 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1320)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 1 (meaning1316 q) (meaning1320 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1320 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1321)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 2 (meaning1317 q) (meaning1321 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1321 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 1318 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1318)) (literal (valuationOf q) (1322)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 3 (meaning1318 q) (meaning1322 q) hs
  change valuationOf q 1318 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 1318 = false ∨ valuation q 1322 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1320 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1309)) (literal (valuationOf q) (1320)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 1 (meaning1309 q) (meaning1320 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1320 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1321)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 1 1 (meaning1309 q) (meaning1316 q) (meaning1321 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1316 = false ∨ valuation q 1321 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1322)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 1 2 (meaning1309 q) (meaning1317 q) (meaning1322 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1317 = false ∨ valuation q 1322 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1323 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1309)) (literal (valuationOf q) (1318)) (literal (valuationOf q) (1323)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 1 3 (meaning1309 q) (meaning1318 q) (meaning1323 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1318 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1318 = false ∨ valuation q 1323 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1321 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1310)) (literal (valuationOf q) (1321)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 2 (meaning1310 q) (meaning1321 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1321 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1322)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 2 1 (meaning1310 q) (meaning1316 q) (meaning1322 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1316 = false ∨ valuation q 1322 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 1310 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1323 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1310)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1323)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 2 2 (meaning1310 q) (meaning1317 q) (meaning1323 q) hs
  change valuationOf q 1310 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 1310 = false ∨ valuation q 1317 = false ∨ valuation q 1323 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1322 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_left (literal (valuationOf q) (1311)) (literal (valuationOf q) (1322)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 3 (meaning1311 q) (meaning1322 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1322 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1323 = true := by
  have hs : count1320 q = (countLit q [-14, -16, -18]) + (countLit q [-20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1323)) (countLit q [-14, -16, -18]) (countLit q [-20, -22, -23, -24]) (count1320 q) 3 1 (meaning1311 q) (meaning1316 q) (meaning1323 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1316 = false ∨ valuation q 1323 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1320 = false ∨ valuationOf q 1327 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1320)) (literal (valuationOf q) (1327)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 1 (meaning1320 q) (meaning1327 q) hs
  change valuationOf q 1320 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1320 = false ∨ valuation q 1327 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1321 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1321)) (literal (valuationOf q) (1328)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 2 (meaning1321 q) (meaning1328 q) hs
  change valuationOf q 1321 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1321 = false ∨ valuation q 1328 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1322)) (literal (valuationOf q) (1329)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 3 (meaning1322 q) (meaning1329 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1329 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_right (literal (valuationOf q) (1323)) (literal (valuationOf q) (1330)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 4 (meaning1323 q) (meaning1330 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1330 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1328 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1328)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 1 1 (meaning1301 q) (meaning1320 q) (meaning1328 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1320 = false ∨ valuation q 1328 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1329)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 1 2 (meaning1301 q) (meaning1321 q) (meaning1329 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1321 = false ∨ valuation q 1329 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1301)) (literal (valuationOf q) (1322)) (literal (valuationOf q) (1330)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 1 3 (meaning1301 q) (meaning1322 q) (meaning1330 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1322 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1322 = false ∨ valuation q 1330 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1329 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1320)) (literal (valuationOf q) (1329)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 2 1 (meaning1302 q) (meaning1320 q) (meaning1329 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1320 = false ∨ valuationOf q 1329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1320 = false ∨ valuation q 1329 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1302 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1330 = true := by
  have hs : count1327 q = (countLit q [-3, -4, -5, -8, -9, -13]) + (countLit q [-14, -16, -18, -20, -22, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13]) (l₂ := [-14, -16, -18, -20, -22, -23, -24])
  have hm := merge_two (literal (valuationOf q) (1302)) (literal (valuationOf q) (1321)) (literal (valuationOf q) (1330)) (countLit q [-3, -4, -5, -8, -9, -13]) (countLit q [-14, -16, -18, -20, -22, -23, -24]) (count1327 q) 2 2 (meaning1302 q) (meaning1321 q) (meaning1330 q) hs
  change valuationOf q 1302 = false ∨ valuationOf q 1321 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1302 = false ∨ valuation q 1321 = false ∨ valuation q 1330 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1340 = true := by
  have hs : count1340 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1340)) (countLit q [-29]) (countLit q [-31]) (count1340 q) 1 (meaningNeg31 q) (meaning1340 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1340 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1340 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1341 = true := by
  have hs : count1340 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1341)) (countLit q [-29]) (countLit q [-31]) (count1340 q) 1 1 (meaningNeg29 q) (meaningNeg31 q) (meaning1341 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1341 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 1341 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1340 = false ∨ valuationOf q 1342 = true := by
  have hs : count1342 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1340)) (literal (valuationOf q) (1342)) (countLit q [-27]) (countLit q [-29, -31]) (count1342 q) 1 (meaning1340 q) (meaning1342 q) hs
  change valuationOf q 1340 = false ∨ valuationOf q 1342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1340 = false ∨ valuation q 1342 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1341 = false ∨ valuationOf q 1343 = true := by
  have hs : count1342 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1341)) (literal (valuationOf q) (1343)) (countLit q [-27]) (countLit q [-29, -31]) (count1342 q) 2 (meaning1341 q) (meaning1343 q) hs
  change valuationOf q 1341 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1341 = false ∨ valuation q 1343 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true := by
  have hs : count1342 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1340)) (literal (valuationOf q) (1343)) (countLit q [-27]) (countLit q [-29, -31]) (count1342 q) 1 1 (meaningNeg27 q) (meaning1340 q) (meaning1343 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1340 = false ∨ valuationOf q 1343 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1340 = false ∨ valuation q 1343 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1341 = false ∨ valuationOf q 1344 = true := by
  have hs : count1342 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (1341)) (literal (valuationOf q) (1344)) (countLit q [-27]) (countLit q [-29, -31]) (count1342 q) 1 2 (meaningNeg27 q) (meaning1341 q) (meaning1344 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1341 = false ∨ valuationOf q 1344 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1341 = false ∨ valuation q 1344 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E090.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112090
