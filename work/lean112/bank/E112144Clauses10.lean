import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83, -84])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1414)) (countLit q [-82]) (countLit q [-83, -84]) (count1414 q) 1 (meaning1412 q) (meaning1414 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1414 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1414)) (countLit q [-82]) (countLit q [-83, -84]) (count1414 q) 1 (meaningNeg82 q) (meaning1414 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1414 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1417)) (countLit q [-86]) (countLit q [-87]) (count1417 q) 1 (meaningNeg86 q) (meaning1417 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1417 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1419)) (countLit q [-89]) (countLit q [-92]) (count1419 q) 1 (meaningNeg92 q) (meaning1419 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1419 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1419)) (countLit q [-89]) (countLit q [-92]) (count1419 q) 1 (meaningNeg89 q) (meaning1419 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1419 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1420 = true := by
  have hs : count1419 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1420)) (countLit q [-89]) (countLit q [-92]) (count1419 q) 1 1 (meaningNeg89 q) (meaningNeg92 q) (meaning1420 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 92 = true ∨ valuation q 1420 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-86, -87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (1419)) (literal (valuationOf q) (1421)) (countLit q [-86, -87]) (countLit q [-89, -92]) (count1421 q) 1 (meaning1419 q) (meaning1421 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1421 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-86, -87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-86, -87]) (countLit q [-89, -92]) (count1421 q) 2 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-86, -87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -92])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1421)) (countLit q [-86, -87]) (countLit q [-89, -92]) (count1421 q) 1 (meaning1417 q) (meaning1421 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1421 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-86, -87]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-86, -87]) (l₂ := [-89, -92])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1422)) (countLit q [-86, -87]) (countLit q [-89, -92]) (count1421 q) 1 1 (meaning1417 q) (meaning1419 q) (meaning1422 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = false ∨ valuation q 1422 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-82, -83, -84]) + (countLit q [-86, -87, -89, -92]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -84]) (l₂ := [-86, -87, -89, -92])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1425)) (countLit q [-82, -83, -84]) (countLit q [-86, -87, -89, -92]) (count1425 q) 1 (meaning1414 q) (meaning1425 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1425 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-82, -83, -84]) + (countLit q [-86, -87, -89, -92]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -84]) (l₂ := [-86, -87, -89, -92])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1426)) (countLit q [-82, -83, -84]) (countLit q [-86, -87, -89, -92]) (count1425 q) 1 1 (meaning1414 q) (meaning1421 q) (meaning1426 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1421 = false ∨ valuation q 1426 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-82, -83, -84]) + (countLit q [-86, -87, -89, -92]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -84]) (l₂ := [-86, -87, -89, -92])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-82, -83, -84]) (countLit q [-86, -87, -89, -92]) (count1425 q) 1 2 (meaning1414 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1432)) (countLit q [-95]) (countLit q [-97]) (count1432 q) 1 (meaningNeg97 q) (meaning1432 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1432 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1434)) (countLit q [-94]) (countLit q [-95, -97]) (count1434 q) 1 (meaning1432 q) (meaning1434 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1434 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1434)) (countLit q [-94]) (countLit q [-95, -97]) (count1434 q) 1 (meaningNeg94 q) (meaning1434 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1434 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1437)) (countLit q [-100]) (countLit q [-102]) (count1437 q) 1 (meaningNeg100 q) (meaning1437 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1437 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1437)) (literal (valuationOf q) (1441)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 (meaning1437 q) (meaning1441 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1441 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-94, -95, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-94, -95, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-94, -95, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1445)) (countLit q [-94, -95, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 (meaning1434 q) (meaning1445 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1445 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-82, -83, -84, -86, -87, -89, -92]) + (countLit q [-94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -84, -86, -87, -89, -92]) (l₂ := [-94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (countLit q [-82, -83, -84, -86, -87, -89, -92]) (countLit q [-94, -95, -97, -100, -102, -103, -105]) (count1452 q) 1 1 (meaning1425 q) (meaning1445 q) (meaning1453 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1445 = false ∨ valuation q 1453 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-82, -83, -84, -86, -87, -89, -92]) + (countLit q [-94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -84, -86, -87, -89, -92]) (l₂ := [-94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (countLit q [-82, -83, -84, -86, -87, -89, -92]) (countLit q [-94, -95, -97, -100, -102, -103, -105]) (count1452 q) 2 1 (meaning1426 q) (meaning1445 q) (meaning1454 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1445 = false ∨ valuation q 1454 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-82, -83, -84, -86, -87, -89, -92]) + (countLit q [-94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -84, -86, -87, -89, -92]) (l₂ := [-94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1455)) (countLit q [-82, -83, -84, -86, -87, -89, -92]) (countLit q [-94, -95, -97, -100, -102, -103, -105]) (count1452 q) 3 1 (meaning1427 q) (meaning1445 q) (meaning1455 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1445 = false ∨ valuation q 1455 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1469)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 3 2 (meaning1401 q) (meaning1453 q) (meaning1469 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1453 = false ∨ valuation q 1469 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1470)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 3 3 (meaning1401 q) (meaning1454 q) (meaning1470 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1454 = false ∨ valuation q 1470 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1470)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 4 2 (meaning1402 q) (meaning1453 q) (meaning1470 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1453 = false ∨ valuation q 1470 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 4 3 (meaning1402 q) (meaning1454 q) (meaning1471 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1454 = false ∨ valuation q 1471 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1472)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 4 4 (meaning1402 q) (meaning1455 q) (meaning1472 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1455 = false ∨ valuation q 1472 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1471)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 5 2 (meaning1403 q) (meaning1453 q) (meaning1471 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1453 = false ∨ valuation q 1471 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1472)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 5 3 (meaning1403 q) (meaning1454 q) (meaning1472 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1454 = false ∨ valuation q 1472 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1472)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 6 2 (meaning1404 q) (meaning1453 q) (meaning1472 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1453 = false ∨ valuation q 1472 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) + (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (l₂ := [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1473)) (countLit q [-54, -56, -58, -60, -63, -66, -67, -69, -70, -74, -76, -77, -78]) (countLit q [-82, -83, -84, -86, -87, -89, -92, -94, -95, -97, -100, -102, -103, -105]) (count1465 q) 6 3 (meaning1404 q) (meaning1454 q) (meaning1473 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1454 = false ∨ valuation q 1473 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E144.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112144
