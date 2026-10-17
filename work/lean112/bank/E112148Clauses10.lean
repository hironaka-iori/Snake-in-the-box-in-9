import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 1344 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -18])
  have hm := merge_right (literal (valuationOf q) (1344)) (literal (valuationOf q) (1346)) (countLit q [-15]) (countLit q [-16, -18]) (count1345 q) 2 (meaning1344 q) (meaning1346 q) hs
  change valuationOf q 1344 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 1344 = false ∨ valuation q 1346 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1345 = true := by
  have hs : count1345 q = (countLit q [-15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1345)) (countLit q [-15]) (countLit q [-16, -18]) (count1345 q) 1 (meaningNeg15 q) (meaning1345 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1345 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1345 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true := by
  have hs : count1345 q = (countLit q [-15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1343)) (literal (valuationOf q) (1346)) (countLit q [-15]) (countLit q [-16, -18]) (count1345 q) 1 1 (meaningNeg15 q) (meaning1343 q) (meaning1346 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1343 = false ∨ valuationOf q 1346 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1343 = false ∨ valuation q 1346 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true := by
  have hs : count1345 q = (countLit q [-15]) + (countLit q [-16, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1344)) (literal (valuationOf q) (1347)) (countLit q [-15]) (countLit q [-16, -18]) (count1345 q) 1 2 (meaningNeg15 q) (meaning1344 q) (meaning1347 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1344 = false ∨ valuationOf q 1347 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1344 = false ∨ valuation q 1347 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-20]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1348)) (countLit q [-20]) (countLit q [-24]) (count1348 q) 1 (meaningNeg24 q) (meaning1348 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1348 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1348 = true := by
  have hs : count1348 q = (countLit q [-20]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1348)) (countLit q [-20]) (countLit q [-24]) (count1348 q) 1 (meaningNeg20 q) (meaning1348 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1348 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1348 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1349 = true := by
  have hs : count1348 q = (countLit q [-20]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1349)) (countLit q [-20]) (countLit q [-24]) (count1348 q) 1 1 (meaningNeg20 q) (meaningNeg24 q) (meaning1349 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 24 = true ∨ valuation q 1349 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1350)) (countLit q [-26]) (countLit q [-28]) (count1350 q) 1 (meaningNeg28 q) (meaning1350 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1350 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1350 = true := by
  have hs : count1350 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1350)) (countLit q [-26]) (countLit q [-28]) (count1350 q) 1 (meaningNeg26 q) (meaning1350 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1350 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-20, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-20, -24]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1352)) (countLit q [-20, -24]) (countLit q [-26, -28]) (count1352 q) 1 (meaning1350 q) (meaning1352 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1352 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1352 = true := by
  have hs : count1352 q = (countLit q [-20, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-20, -24]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1348)) (literal (valuationOf q) (1352)) (countLit q [-20, -24]) (countLit q [-26, -28]) (count1352 q) 1 (meaning1348 q) (meaning1352 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1352 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1348 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-20, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-20, -24]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1348)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1353)) (countLit q [-20, -24]) (countLit q [-26, -28]) (count1352 q) 1 1 (meaning1348 q) (meaning1350 q) (meaning1353 q) hs
  change valuationOf q 1348 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1348 = false ∨ valuation q 1350 = false ∨ valuation q 1353 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1353 = true := by
  have hs : count1352 q = (countLit q [-20, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-20, -24]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (1349)) (literal (valuationOf q) (1353)) (countLit q [-20, -24]) (countLit q [-26, -28]) (count1352 q) 2 (meaning1349 q) (meaning1353 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1353 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-20, -24]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-20, -24]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (1349)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1354)) (countLit q [-20, -24]) (countLit q [-26, -28]) (count1352 q) 2 1 (meaning1349 q) (meaning1350 q) (meaning1354 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1350 = false ∨ valuation q 1354 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1352 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1352)) (literal (valuationOf q) (1356)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 1 (meaning1352 q) (meaning1356 q) hs
  change valuationOf q 1352 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1352 = false ∨ valuation q 1356 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1353)) (literal (valuationOf q) (1357)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 2 (meaning1353 q) (meaning1357 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1357 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_right (literal (valuationOf q) (1354)) (literal (valuationOf q) (1358)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 3 (meaning1354 q) (meaning1358 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1358 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1345)) (literal (valuationOf q) (1356)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 1 (meaning1345 q) (meaning1356 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1356 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1357)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 1 1 (meaning1345 q) (meaning1352 q) (meaning1357 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1352 = false ∨ valuation q 1357 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1358)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 1 2 (meaning1345 q) (meaning1353 q) (meaning1358 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1353 = false ∨ valuation q 1358 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 1345 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1359 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1345)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1359)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 1 3 (meaning1345 q) (meaning1354 q) (meaning1359 q) hs
  change valuationOf q 1345 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 1345 = false ∨ valuation q 1354 = false ∨ valuation q 1359 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1346)) (literal (valuationOf q) (1357)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 2 (meaning1346 q) (meaning1357 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1357 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1346)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1358)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 2 1 (meaning1346 q) (meaning1352 q) (meaning1358 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1352 = false ∨ valuation q 1358 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1346 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1359 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1346)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1359)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 2 2 (meaning1346 q) (meaning1353 q) (meaning1359 q) hs
  change valuationOf q 1346 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1346 = false ∨ valuation q 1353 = false ∨ valuation q 1359 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1358 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_left (literal (valuationOf q) (1347)) (literal (valuationOf q) (1358)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 3 (meaning1347 q) (meaning1358 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1358 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 1347 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1359 = true := by
  have hs : count1356 q = (countLit q [-15, -16, -18]) + (countLit q [-20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -18]) (l₂ := [-20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1347)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1359)) (countLit q [-15, -16, -18]) (countLit q [-20, -24, -26, -28]) (count1356 q) 3 1 (meaning1347 q) (meaning1352 q) (meaning1359 q) hs
  change valuationOf q 1347 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 1347 = false ∨ valuation q 1352 = false ∨ valuation q 1359 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1366 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1366)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 2 2 (meaning1338 q) (meaning1357 q) (meaning1366 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1357 = false ∨ valuation q 1366 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1367 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1367)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 2 3 (meaning1338 q) (meaning1358 q) (meaning1367 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1358 = false ∨ valuation q 1367 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 1338 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1368 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1338)) (literal (valuationOf q) (1359)) (literal (valuationOf q) (1368)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 2 4 (meaning1338 q) (meaning1359 q) (meaning1368 q) hs
  change valuationOf q 1338 = false ∨ valuationOf q 1359 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 1338 = false ∨ valuation q 1359 = false ∨ valuation q 1368 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1366 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1366)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 3 1 (meaning1339 q) (meaning1356 q) (meaning1366 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1356 = false ∨ valuation q 1366 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1367 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1367)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 3 2 (meaning1339 q) (meaning1357 q) (meaning1367 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1357 = false ∨ valuation q 1367 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 1339 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1368 = true := by
  have hs : count1363 q = (countLit q [-1, -2, -6, -10, -12, -13]) + (countLit q [-15, -16, -18, -20, -24, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -10, -12, -13]) (l₂ := [-15, -16, -18, -20, -24, -26, -28])
  have hm := merge_two (literal (valuationOf q) (1339)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1368)) (countLit q [-1, -2, -6, -10, -12, -13]) (countLit q [-15, -16, -18, -20, -24, -26, -28]) (count1363 q) 3 3 (meaning1339 q) (meaning1358 q) (meaning1368 q) hs
  change valuationOf q 1339 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 1339 = false ∨ valuation q 1358 = false ∨ valuation q 1368 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E148.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112148
