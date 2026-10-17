import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-87]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1422)) (countLit q [-87]) (countLit q [-91]) (count1422 q) 1 (meaningNeg91 q) (meaning1422 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1422 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-87]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1422)) (countLit q [-87]) (countLit q [-91]) (count1422 q) 1 (meaningNeg87 q) (meaning1422 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1422 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-87]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1423)) (countLit q [-87]) (countLit q [-91]) (count1422 q) 1 1 (meaningNeg87 q) (meaningNeg91 q) (meaning1423 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 91 = true ∨ valuation q 1423 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-85]) + (countLit q [-87, -91]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -91])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1424)) (countLit q [-85]) (countLit q [-87, -91]) (count1424 q) 1 (meaning1422 q) (meaning1424 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1424 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1425 = true := by
  have hs : count1424 q = (countLit q [-85]) + (countLit q [-87, -91]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -91])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1425)) (countLit q [-85]) (countLit q [-87, -91]) (count1424 q) 2 (meaning1423 q) (meaning1425 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1425 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-85]) + (countLit q [-87, -91]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -91])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1424)) (countLit q [-85]) (countLit q [-87, -91]) (count1424 q) 1 (meaningNeg85 q) (meaning1424 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1424 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true := by
  have hs : count1424 q = (countLit q [-85]) + (countLit q [-87, -91]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87, -91])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1425)) (countLit q [-85]) (countLit q [-87, -91]) (count1424 q) 1 1 (meaningNeg85 q) (meaning1422 q) (meaning1425 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1422 = false ∨ valuation q 1425 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 1 (meaning1424 q) (meaning1427 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1427 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_right (literal (valuationOf q) (1425)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 2 (meaning1425 q) (meaning1428 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1428 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 1 1 (meaning1419 q) (meaning1424 q) (meaning1428 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1424 = false ∨ valuation q 1428 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1429)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 1 2 (meaning1419 q) (meaning1425 q) (meaning1429 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1425 = false ∨ valuation q 1429 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_left (literal (valuationOf q) (1420)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 2 (meaning1420 q) (meaning1428 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1428 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1429)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 2 1 (meaning1420 q) (meaning1424 q) (meaning1429 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1424 = false ∨ valuation q 1429 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1430)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 2 2 (meaning1420 q) (meaning1425 q) (meaning1430 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1425 = false ∨ valuation q 1430 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-85, -87, -91]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-85, -87, -91])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1425)) (literal (valuationOf q) (1431)) (countLit q [-81, -82, -84]) (countLit q [-85, -87, -91]) (count1427 q) 3 2 (meaning1421 q) (meaning1425 q) (meaning1431 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1425 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1425 = false ∨ valuation q 1431 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1433)) (countLit q [-94]) (countLit q [-96]) (count1433 q) 1 (meaningNeg96 q) (meaning1433 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1433 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1433)) (countLit q [-94]) (countLit q [-96]) (count1433 q) 1 (meaningNeg94 q) (meaning1433 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1433 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1434)) (countLit q [-94]) (countLit q [-96]) (count1433 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1434 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1434 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-92]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (countLit q [-92]) (countLit q [-94, -96]) (count1435 q) 1 (meaning1433 q) (meaning1435 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-92]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94, -96])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (countLit q [-92]) (countLit q [-94, -96]) (count1435 q) 2 (meaning1434 q) (meaning1436 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-92]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94, -96])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1435)) (countLit q [-92]) (countLit q [-94, -96]) (count1435 q) 1 (meaningNeg92 q) (meaning1435 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1435 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-92]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (countLit q [-92]) (countLit q [-94, -96]) (count1435 q) 1 1 (meaningNeg92 q) (meaning1433 q) (meaning1436 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1433 = false ∨ valuation q 1436 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1434 = false ∨ valuationOf q 1437 = true := by
  have hs : count1435 q = (countLit q [-92]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1437)) (countLit q [-92]) (countLit q [-94, -96]) (count1435 q) 1 2 (meaningNeg92 q) (meaning1434 q) (meaning1437 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1434 = false ∨ valuation q 1437 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1438)) (countLit q [-98]) (countLit q [-99]) (count1438 q) 1 (meaningNeg99 q) (meaning1438 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1438 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1438)) (countLit q [-98]) (countLit q [-99]) (count1438 q) 1 (meaningNeg98 q) (meaning1438 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1438 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1439 = true := by
  have hs : count1438 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1439)) (countLit q [-98]) (countLit q [-99]) (count1438 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1439 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1439 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-103]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1440)) (countLit q [-103]) (countLit q [-106]) (count1440 q) 1 (meaningNeg106 q) (meaning1440 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1440 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-103]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1440)) (countLit q [-103]) (countLit q [-106]) (count1440 q) 1 (meaningNeg103 q) (meaning1440 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1440 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1441 = true := by
  have hs : count1440 q = (countLit q [-103]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1441)) (countLit q [-103]) (countLit q [-106]) (count1440 q) 1 1 (meaningNeg103 q) (meaningNeg106 q) (meaning1441 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 106 = true ∨ valuation q 1441 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1442)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 1 (meaning1440 q) (meaning1442 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1442 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 2 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-98, -99]) + (countLit q [-103, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-103, -106])
  have hm := merge_left (literal (valuationOf q) (1438)) (literal (valuationOf q) (1442)) (countLit q [-98, -99]) (countLit q [-103, -106]) (count1442 q) 1 (meaning1438 q) (meaning1442 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1442 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E150.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112150
