import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 2 2 (meaning1415 q) (meaning1422 q) (meaning1428 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1422 = false ∨ valuation q 1428 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1429)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 2 3 (meaning1415 q) (meaning1423 q) (meaning1429 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1423 = false ∨ valuation q 1429 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_left (literal (valuationOf q) (1416)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 3 (meaning1416 q) (meaning1427 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1427 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1428 = true := by
  have hs : count1425 q = (countLit q [-81, -82, -83]) + (countLit q [-86, -88, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83]) (l₂ := [-86, -88, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -83]) (countLit q [-86, -88, -90, -93]) (count1425 q) 3 1 (meaning1416 q) (meaning1421 q) (meaning1428 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1421 = false ∨ valuation q 1428 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1432)) (countLit q [-96]) (countLit q [-97]) (count1432 q) 1 (meaningNeg97 q) (meaning1432 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1432 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1433)) (countLit q [-96]) (countLit q [-97]) (count1432 q) 1 1 (meaningNeg96 q) (meaningNeg97 q) (meaning1433 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 97 = true ∨ valuation q 1433 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-95]) + (countLit q [-96, -97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96, -97])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1434)) (countLit q [-95]) (countLit q [-96, -97]) (count1434 q) 1 (meaning1432 q) (meaning1434 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1434 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-95]) + (countLit q [-96, -97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96, -97])
  have hm := merge_right (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (countLit q [-95]) (countLit q [-96, -97]) (count1434 q) 2 (meaning1433 q) (meaning1435 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-95]) + (countLit q [-96, -97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96, -97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1434)) (countLit q [-95]) (countLit q [-96, -97]) (count1434 q) 1 (meaningNeg95 q) (meaning1434 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1434 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-95]) + (countLit q [-96, -97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96, -97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (countLit q [-95]) (countLit q [-96, -97]) (count1434 q) 1 2 (meaningNeg95 q) (meaning1433 q) (meaning1436 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1433 = false ∨ valuation q 1436 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1437)) (countLit q [-100]) (countLit q [-102]) (count1437 q) 1 (meaningNeg102 q) (meaning1437 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1437 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1437)) (countLit q [-100]) (countLit q [-102]) (count1437 q) 1 (meaningNeg100 q) (meaning1437 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1437 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1439)) (countLit q [-103]) (countLit q [-105]) (count1439 q) 1 (meaningNeg105 q) (meaning1439 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1439 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1439 = true := by
  have hs : count1439 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1439)) (countLit q [-103]) (countLit q [-105]) (count1439 q) 1 (meaningNeg103 q) (meaning1439 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1439 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1440 = true := by
  have hs : count1439 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1440)) (countLit q [-103]) (countLit q [-105]) (count1439 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1440 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1440 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1439)) (literal (valuationOf q) (1441)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 (meaning1439 q) (meaning1441 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1441 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1437)) (literal (valuationOf q) (1441)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 (meaning1437 q) (meaning1441 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1441 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1439)) (literal (valuationOf q) (1442)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 1 (meaning1437 q) (meaning1439 q) (meaning1442 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1439 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1439 = false ∨ valuation q 1442 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true := by
  have hs : count1441 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1440)) (literal (valuationOf q) (1443)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1441 q) 1 2 (meaning1437 q) (meaning1440 q) (meaning1443 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1440 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1440 = false ∨ valuation q 1443 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 2 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 3 (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1447 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1445)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 (meaning1434 q) (meaning1445 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1445 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1446)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 1 1 (meaning1434 q) (meaning1441 q) (meaning1446 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1441 = false ∨ valuation q 1446 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1447)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 2 1 (meaning1435 q) (meaning1441 q) (meaning1447 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1441 = false ∨ valuation q 1447 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-95, -96, -97]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1436)) (literal (valuationOf q) (1447)) (countLit q [-95, -96, -97]) (countLit q [-100, -102, -103, -105]) (count1445 q) 3 (meaning1436 q) (meaning1447 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1447 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 2 1 (meaning1426 q) (meaning1445 q) (meaning1454 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1445 = false ∨ valuation q 1454 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 2 2 (meaning1426 q) (meaning1446 q) (meaning1455 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1446 = false ∨ valuation q 1455 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 2 3 (meaning1426 q) (meaning1447 q) (meaning1456 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1447 = false ∨ valuation q 1456 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1455)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 3 1 (meaning1427 q) (meaning1445 q) (meaning1455 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1445 = false ∨ valuation q 1455 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 3 2 (meaning1427 q) (meaning1446 q) (meaning1456 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1446 = false ∨ valuation q 1456 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-81, -82, -83, -86, -88, -90, -93]) + (countLit q [-95, -96, -97, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -83, -86, -88, -90, -93]) (l₂ := [-95, -96, -97, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1456)) (countLit q [-81, -82, -83, -86, -88, -90, -93]) (countLit q [-95, -96, -97, -100, -102, -103, -105]) (count1452 q) 4 1 (meaning1428 q) (meaning1445 q) (meaning1456 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1445 = false ∨ valuation q 1456 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E246.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112246
