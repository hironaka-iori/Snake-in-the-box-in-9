import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (385)) (countLit q [196]) (countLit q [197, 198]) (count385 q) 1 (meaning196 q) (meaning385 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 385 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (387)) (countLit q [200]) (countLit q [201]) (count387 q) 1 (meaning200 q) (meaning387 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 387 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200, 201]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [196, 197, 198]) + (countLit q [199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198]) (l₂ := [199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (391)) (countLit q [196, 197, 198]) (countLit q [199, 200, 201]) (count391 q) 1 (meaning385 q) (meaning391 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 391 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (393)) (countLit q [203]) (countLit q [204]) (count393 q) 1 (meaning203 q) (meaning393 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 393 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [202]) (countLit q [203, 204]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (395)) (countLit q [202]) (countLit q [203, 204]) (count395 q) 1 (meaning202 q) (meaning395 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 395 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_two (literal (valuationOf q) (202)) (literal (valuationOf q) (393)) (literal (valuationOf q) (396)) (countLit q [202]) (countLit q [203, 204]) (count395 q) 1 1 (meaning202 q) (meaning393 q) (meaning396 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 393 = false ∨ valuation q 396 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_left (literal (valuationOf q) (205)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning205 q) (meaning397 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 397 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [207]) + (countLit q [208]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208])
  have hm := merge_left (literal (valuationOf q) (207)) (literal (valuationOf q) (399)) (countLit q [207]) (countLit q [208]) (count399 q) 1 (meaning207 q) (meaning399 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 399 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (401)) (literal (valuationOf q) (404)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 1 (meaning395 q) (meaning401 q) (meaning404 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 401 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 401 = false ∨ valuation q 404 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 396 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (396)) (literal (valuationOf q) (404)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 2 (meaning396 q) (meaning404 q) hs
  change valuationOf q 396 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 396 = false ∨ valuation q 404 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (404)) (literal (valuationOf q) (406)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 2 (meaning404 q) (meaning406 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 406 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning391 q) (meaning405 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 405 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (391)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 1 (meaning391 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (406)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning406 q) (meaning408 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 408 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning381 q) (meaning407 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 407 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (405)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 1 (meaning381 q) (meaning405 q) (meaning408 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 405 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 405 = false ∨ valuation q 408 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (408)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning382 q) (meaning408 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 408 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (408)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning408 q) (meaning410 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 410 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (409)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning357 q) (meaning409 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 409 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (357)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 1 (meaning357 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 358 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (358)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning358 q) (meaning410 q) hs
  change valuationOf q 358 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 410 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E225.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112225
