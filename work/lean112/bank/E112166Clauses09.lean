import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (359)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183, 184]) (count359 q) 1 (meaning351 q) (meaning359 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 359 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (373)) (countLit q [178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count373 q) 1 (meaning359 q) (meaning373 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 373 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (375)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning347 q) (meaning375 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 375 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (376)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 2 (meaning348 q) (meaning376 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 376 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193, 194])
  have hm := merge_left (literal (valuationOf q) (192)) (literal (valuationOf q) (379)) (countLit q [192]) (countLit q [193, 194]) (count379 q) 1 (meaning192 q) (meaning379 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 379 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuationOf q) (197)) (literal (valuationOf q) (381)) (countLit q [196]) (countLit q [197]) (count381 q) 1 (meaning197 q) (meaning381 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 381 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [195]) (countLit q [196, 197]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (385)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197]) (count385 q) 1 (meaning379 q) (meaning385 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 385 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (383)) (literal (valuationOf q) (386)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197]) (count385 q) 1 1 (meaning379 q) (meaning383 q) (meaning386 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 383 = false ∨ valuation q 386 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_right (literal (valuationOf q) (200)) (literal (valuationOf q) (387)) (countLit q [199]) (countLit q [200]) (count387 q) 1 (meaning200 q) (meaning387 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 387 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199, 200])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [198]) (countLit q [199, 200]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (397)) (countLit q [198, 199, 200]) (countLit q [201, 202, 203, 204]) (count397 q) 1 (meaning389 q) (meaning397 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 397 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204])
  have hm := merge_two (literal (valuationOf q) (385)) (literal (valuationOf q) (397)) (literal (valuationOf q) (400)) (countLit q [192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204]) (count399 q) 1 1 (meaning385 q) (meaning397 q) (meaning400 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 397 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 397 = false ∨ valuation q 400 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 386 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (386)) (literal (valuationOf q) (400)) (countLit q [192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204]) (count399 q) 2 (meaning386 q) (meaning400 q) hs
  change valuationOf q 386 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 386 = false ∨ valuation q 400 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (428)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count427 q) 2 (meaning400 q) (meaning428 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 428 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (429)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 1 (meaning375 q) (meaning429 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 429 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (376)) (literal (valuationOf q) (430)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count429 q) 2 (meaning376 q) (meaning430 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 430 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 430 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_right (literal (valuationOf q) (430)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 2 (meaning430 q) (meaning432 q) hs
  change valuationOf q 430 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 430 = false ∨ valuation q 432 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (429)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 1 1 (meaning323 q) (meaning429 q) (meaning432 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 429 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 429 = false ∨ valuation q 432 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (432)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]) (count431 q) 2 (meaning324 q) (meaning432 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 432 = true := counterClause311 (baseVal q)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 432 = false := by
  rw [value432]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count431 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause313 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1291)) (countLit q [-3]) (countLit q [-5]) (count1291 q) 1 (meaningNeg5 q) (meaning1291 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1291 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1291)) (countLit q [-3]) (countLit q [-5]) (count1291 q) 1 (meaningNeg3 q) (meaning1291 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1291 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1292 = true := by
  have hs : count1291 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1292)) (countLit q [-3]) (countLit q [-5]) (count1291 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1292 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1292 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1291)) (literal (valuationOf q) (1293)) (countLit q [-2]) (countLit q [-3, -5]) (count1293 q) 1 (meaning1291 q) (meaning1293 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1293 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1292)) (literal (valuationOf q) (1294)) (countLit q [-2]) (countLit q [-3, -5]) (count1293 q) 2 (meaning1292 q) (meaning1294 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1294 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1293)) (countLit q [-2]) (countLit q [-3, -5]) (count1293 q) 1 (meaningNeg2 q) (meaning1293 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1293 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1291 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1291)) (literal (valuationOf q) (1294)) (countLit q [-2]) (countLit q [-3, -5]) (count1293 q) 1 1 (meaningNeg2 q) (meaning1291 q) (meaning1294 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1291 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1291 = false ∨ valuation q 1294 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1292 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1292)) (literal (valuationOf q) (1295)) (countLit q [-2]) (countLit q [-3, -5]) (count1293 q) 1 2 (meaningNeg2 q) (meaning1292 q) (meaning1295 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1292 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1292 = false ∨ valuation q 1295 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E166.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112166
