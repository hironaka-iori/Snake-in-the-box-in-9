import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 1 1 (meaning373 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuationOf q) (197)) (literal (valuationOf q) (381)) (countLit q [196]) (countLit q [197]) (count381 q) 1 (meaning197 q) (meaning381 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 381 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [196]) (countLit q [197]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 197 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_two (literal (valuationOf q) (196)) (literal (valuationOf q) (197)) (literal (valuationOf q) (382)) (countLit q [196]) (countLit q [197]) (count381 q) 1 1 (meaning196 q) (meaning197 q) (meaning382 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 197 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 197 = false ∨ valuation q 382 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [194, 195]) (countLit q [196, 197]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (382)) (literal (valuationOf q) (384)) (countLit q [194, 195]) (countLit q [196, 197]) (count383 q) 2 (meaning382 q) (meaning384 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 384 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 384 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (384)) (literal (valuationOf q) (386)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count385 q) 2 (meaning384 q) (meaning386 q) hs
  change valuationOf q 384 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 384 = false ∨ valuation q 386 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count385 q) 1 (meaning377 q) (meaning385 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 385 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (383)) (literal (valuationOf q) (386)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count385 q) 1 1 (meaning377 q) (meaning383 q) (meaning386 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 383 = false ∨ valuation q 386 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [190, 191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (386)) (countLit q [190, 191, 192, 193]) (countLit q [194, 195, 196, 197]) (count385 q) 2 (meaning378 q) (meaning386 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 386 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 386 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (386)) (literal (valuationOf q) (388)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count387 q) 2 (meaning386 q) (meaning388 q) hs
  change valuationOf q 386 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 386 = false ∨ valuation q 388 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (387)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count387 q) 1 (meaning371 q) (meaning387 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 387 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_two (literal (valuationOf q) (371)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count387 q) 1 1 (meaning371 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [183, 184, 185, 186, 187, 188, 189]) + (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189]) (l₂ := [190, 191, 192, 193, 194, 195, 196, 197])
  have hm := merge_left (literal (valuationOf q) (372)) (literal (valuationOf q) (388)) (countLit q [183, 184, 185, 186, 187, 188, 189]) (countLit q [190, 191, 192, 193, 194, 195, 196, 197]) (count387 q) 2 (meaning372 q) (meaning388 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 388 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_right (literal (valuationOf q) (202)) (literal (valuationOf q) (393)) (countLit q [201]) (countLit q [202]) (count393 q) 1 (meaning202 q) (meaning393 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 393 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (393)) (countLit q [201]) (countLit q [202]) (count393 q) 1 (meaning201 q) (meaning393 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 393 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 202 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [201]) + (countLit q [202]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202])
  have hm := merge_two (literal (valuationOf q) (201)) (literal (valuationOf q) (202)) (literal (valuationOf q) (394)) (countLit q [201]) (countLit q [202]) (count393 q) 1 1 (meaning201 q) (meaning202 q) (meaning394 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 202 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 202 = false ∨ valuation q 394 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning203 q) (meaning395 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 395 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning393 q) (meaning397 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 397 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = false ∨ valuationOf q 398 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_two (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (literal (valuationOf q) (398)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 1 (meaning393 q) (meaning395 q) (meaning398 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = false ∨ valuationOf q 398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = false ∨ valuation q 398 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 398 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (394)) (literal (valuationOf q) (398)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 2 (meaning394 q) (meaning398 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 398 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 398 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (398)) (literal (valuationOf q) (400)) (countLit q [198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 2 (meaning398 q) (meaning400 q) hs
  change valuationOf q 398 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 398 = false ∨ valuation q 400 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (401)) (countLit q [205]) (countLit q [206]) (count401 q) 1 (meaning206 q) (meaning401 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 401 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_right (literal (valuationOf q) (208)) (literal (valuationOf q) (403)) (countLit q [207]) (countLit q [208]) (count403 q) 1 (meaning208 q) (meaning403 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 403 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [205, 206]) (countLit q [207, 208]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (405)) (countLit q [205, 206]) (countLit q [207, 208]) (count405 q) 1 (meaning401 q) (meaning405 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 405 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_two (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [205, 206]) (countLit q [207, 208]) (count405 q) 1 1 (meaning401 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (407)) (countLit q [209]) (countLit q [210]) (count407 q) 1 (meaning210 q) (meaning407 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 407 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E019.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112019
