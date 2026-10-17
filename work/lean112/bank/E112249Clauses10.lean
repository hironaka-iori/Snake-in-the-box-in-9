import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1381)) (countLit q [-64]) (countLit q [-66]) (count1381 q) 1 (meaningNeg66 q) (meaning1381 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1381 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1381)) (countLit q [-64]) (countLit q [-66]) (count1381 q) 1 (meaningNeg64 q) (meaning1381 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1381 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1382)) (countLit q [-64]) (countLit q [-66]) (count1381 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1382 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1382 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-62]) (countLit q [-64, -66]) (count1383 q) 1 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1382)) (literal (valuationOf q) (1384)) (countLit q [-62]) (countLit q [-64, -66]) (count1383 q) 2 (meaning1382 q) (meaning1384 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1384 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1383 = true := by
  have hs : count1383 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1383)) (countLit q [-62]) (countLit q [-64, -66]) (count1383 q) 1 (meaningNeg62 q) (meaning1383 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1383 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1383 q = (countLit q [-62]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-62]) (countLit q [-64, -66]) (count1383 q) 1 1 (meaningNeg62 q) (meaning1381 q) (meaning1384 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-54, -56, -59]) + (countLit q [-62, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-62, -64, -66])
  have hm := merge_right (literal (valuationOf q) (1383)) (literal (valuationOf q) (1386)) (countLit q [-54, -56, -59]) (countLit q [-62, -64, -66]) (count1386 q) 1 (meaning1383 q) (meaning1386 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1386 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-54, -56, -59]) + (countLit q [-62, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-62, -64, -66])
  have hm := merge_right (literal (valuationOf q) (1384)) (literal (valuationOf q) (1387)) (countLit q [-54, -56, -59]) (countLit q [-62, -64, -66]) (count1386 q) 2 (meaning1384 q) (meaning1387 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1387 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-54, -56, -59]) + (countLit q [-62, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-62, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1387)) (countLit q [-54, -56, -59]) (countLit q [-62, -64, -66]) (count1386 q) 1 1 (meaning1378 q) (meaning1383 q) (meaning1387 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1383 = false ∨ valuation q 1387 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-54, -56, -59]) + (countLit q [-62, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-62, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (countLit q [-54, -56, -59]) (countLit q [-62, -64, -66]) (count1386 q) 2 1 (meaning1379 q) (meaning1383 q) (meaning1388 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1383 = false ∨ valuation q 1388 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1389 = true := by
  have hs : count1386 q = (countLit q [-54, -56, -59]) + (countLit q [-62, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-62, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1389)) (countLit q [-54, -56, -59]) (countLit q [-62, -64, -66]) (count1386 q) 2 2 (meaning1379 q) (meaning1384 q) (meaning1389 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1384 = false ∨ valuation q 1389 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-68]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1392)) (countLit q [-68]) (countLit q [-72]) (count1392 q) 1 (meaningNeg72 q) (meaning1392 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1392 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-68]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1392)) (countLit q [-68]) (countLit q [-72]) (count1392 q) 1 (meaningNeg68 q) (meaning1392 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1392 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1394 = true := by
  have hs : count1394 q = (countLit q [-67]) + (countLit q [-68, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68, -72])
  have hm := merge_right (literal (valuationOf q) (1392)) (literal (valuationOf q) (1394)) (countLit q [-67]) (countLit q [-68, -72]) (count1394 q) 1 (meaning1392 q) (meaning1394 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1394 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1394 = true := by
  have hs : count1394 q = (countLit q [-67]) + (countLit q [-68, -72]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68, -72])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1394)) (countLit q [-67]) (countLit q [-68, -72]) (count1394 q) 1 (meaningNeg67 q) (meaning1394 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1394 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1397)) (countLit q [-78]) (countLit q [-80]) (count1397 q) 1 (meaningNeg80 q) (meaning1397 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1397 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1397)) (countLit q [-78]) (countLit q [-80]) (count1397 q) 1 (meaningNeg78 q) (meaning1397 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1397 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1398 = true := by
  have hs : count1397 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1398)) (countLit q [-78]) (countLit q [-80]) (count1397 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning1398 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 1398 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-74]) (countLit q [-78, -80]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1398)) (literal (valuationOf q) (1400)) (countLit q [-74]) (countLit q [-78, -80]) (count1399 q) 2 (meaning1398 q) (meaning1400 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1400 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1399)) (countLit q [-74]) (countLit q [-78, -80]) (count1399 q) 1 (meaningNeg74 q) (meaning1399 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1399 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-74]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-74]) (countLit q [-78, -80]) (count1399 q) 1 1 (meaningNeg74 q) (meaning1397 q) (meaning1400 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-67, -68, -72]) + (countLit q [-74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -72]) (l₂ := [-74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1399)) (literal (valuationOf q) (1402)) (countLit q [-67, -68, -72]) (countLit q [-74, -78, -80]) (count1402 q) 1 (meaning1399 q) (meaning1402 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1402 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-67, -68, -72]) + (countLit q [-74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -72]) (l₂ := [-74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1403)) (countLit q [-67, -68, -72]) (countLit q [-74, -78, -80]) (count1402 q) 2 (meaning1400 q) (meaning1403 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1403 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-67, -68, -72]) + (countLit q [-74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -72]) (l₂ := [-74, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1394)) (literal (valuationOf q) (1402)) (countLit q [-67, -68, -72]) (countLit q [-74, -78, -80]) (count1402 q) 1 (meaning1394 q) (meaning1402 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1402 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-67, -68, -72]) + (countLit q [-74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -72]) (l₂ := [-74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-67, -68, -72]) (countLit q [-74, -78, -80]) (count1402 q) 1 1 (meaning1394 q) (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1399 = false ∨ valuation q 1403 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1404 = true := by
  have hs : count1402 q = (countLit q [-67, -68, -72]) + (countLit q [-74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-67, -68, -72]) (l₂ := [-74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1404)) (countLit q [-67, -68, -72]) (countLit q [-74, -78, -80]) (count1402 q) 1 2 (meaning1394 q) (meaning1400 q) (meaning1404 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1400 = false ∨ valuation q 1404 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1408)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 1 (meaning1402 q) (meaning1408 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1408 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1409 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1409)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 2 (meaning1403 q) (meaning1409 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1409 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1410 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1410)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 3 (meaning1404 q) (meaning1410 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1410 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1386)) (literal (valuationOf q) (1408)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 1 (meaning1386 q) (meaning1408 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1408 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E249.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112249
