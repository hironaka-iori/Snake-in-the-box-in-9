import E112094Semantics
import B112E094Inputs
namespace Snake9.Regrowth.E112094
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [202]) (countLit q [203, 204]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203, 204])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (395)) (countLit q [202]) (countLit q [203, 204]) (count395 q) 1 (meaning202 q) (meaning395 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 395 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_right (literal (valuationOf q) (206)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning206 q) (meaning397 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 397 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [205, 206]) + (countLit q [207, 208]) := List.countP_append (p := literal q) (l₁ := [205, 206]) (l₂ := [207, 208])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [205, 206]) (countLit q [207, 208]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [202, 203, 204]) + (countLit q [205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204]) (l₂ := [205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (403)) (countLit q [202, 203, 204]) (countLit q [205, 206, 207, 208]) (count403 q) 1 (meaning395 q) (meaning403 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 403 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (405)) (countLit q [196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count405 q) 1 (meaning391 q) (meaning405 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 405 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (407)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning381 q) (meaning407 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 407 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (409)) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning357 q) (meaning409 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 409 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (357)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 1 (meaning357 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 1 1 (meaning307 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning308 q) (meaning412 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 412 = true := counterClause304 (baseVal q)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause306 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 697 = true := by
  have hs : count697 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (697)) (countLit q [-2]) (countLit q [-4]) (count697 q) 1 (meaningNeg4 q) (meaning697 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 697 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 697 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 697 = false ∨ valuationOf q 700 = true := by
  have hs : count699 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (697)) (literal (valuationOf q) (700)) (countLit q [-1]) (countLit q [-2, -4]) (count699 q) 1 1 (meaningNeg1 q) (meaning697 q) (meaning700 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 697 = false ∨ valuationOf q 700 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 697 = false ∨ valuation q 700 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 700 = false ∨ valuationOf q 708 = true := by
  have hs : count707 q = (countLit q [-1, -2, -4]) + (countLit q [-7, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-7, -10, -11])
  have hm := merge_left (literal (valuationOf q) (700)) (literal (valuationOf q) (708)) (countLit q [-1, -2, -4]) (countLit q [-7, -10, -11]) (count707 q) 2 (meaning700 q) (meaning708 q) hs
  change valuationOf q 700 = false ∨ valuationOf q 708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 700 = false ∨ valuation q 708 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 718 = true := by
  have hs : count718 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (718)) (countLit q [-21]) (countLit q [-23]) (count718 q) 1 (meaningNeg23 q) (meaning718 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 718 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 718 = false ∨ valuationOf q 720 = true := by
  have hs : count720 q = (countLit q [-19]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21, -23])
  have hm := merge_right (literal (valuationOf q) (718)) (literal (valuationOf q) (720)) (countLit q [-19]) (countLit q [-21, -23]) (count720 q) 1 (meaning718 q) (meaning720 q) hs
  change valuationOf q 718 = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 718 = false ∨ valuation q 720 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 723 = true := by
  have hs : count723 q = (countLit q [-14, -16, -18]) + (countLit q [-19, -21, -23]) := List.countP_append (p := literal q) (l₁ := [-14, -16, -18]) (l₂ := [-19, -21, -23])
  have hm := merge_right (literal (valuationOf q) (720)) (literal (valuationOf q) (723)) (countLit q [-14, -16, -18]) (countLit q [-19, -21, -23]) (count723 q) 1 (meaning720 q) (meaning723 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 723 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 723 = false ∨ valuationOf q 729 = true := by
  have hs : count729 q = (countLit q [-1, -2, -4, -7, -10, -11]) + (countLit q [-14, -16, -18, -19, -21, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11]) (l₂ := [-14, -16, -18, -19, -21, -23])
  have hm := merge_right (literal (valuationOf q) (723)) (literal (valuationOf q) (729)) (countLit q [-1, -2, -4, -7, -10, -11]) (countLit q [-14, -16, -18, -19, -21, -23]) (count729 q) 1 (meaning723 q) (meaning729 q) hs
  change valuationOf q 723 = false ∨ valuationOf q 729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 723 = false ∨ valuation q 729 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 708 = false ∨ valuationOf q 730 = true := by
  have hs : count729 q = (countLit q [-1, -2, -4, -7, -10, -11]) + (countLit q [-14, -16, -18, -19, -21, -23]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -7, -10, -11]) (l₂ := [-14, -16, -18, -19, -21, -23])
  have hm := merge_left (literal (valuationOf q) (708)) (literal (valuationOf q) (730)) (countLit q [-1, -2, -4, -7, -10, -11]) (countLit q [-14, -16, -18, -19, -21, -23]) (count729 q) 2 (meaning708 q) (meaning730 q) hs
  change valuationOf q 708 = false ∨ valuationOf q 730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 708 = false ∨ valuation q 730 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 740 = true := by
  have hs : count740 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (740)) (countLit q [-27]) (countLit q [-30]) (count740 q) 1 (meaningNeg27 q) (meaning740 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 740 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 740 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 30 = true ∨ valuationOf q 741 = true := by
  have hs : count740 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (741)) (countLit q [-27]) (countLit q [-30]) (count740 q) 1 1 (meaningNeg27 q) (meaningNeg30 q) (meaning741 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 741 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 740 = false ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -30])
  have hm := merge_right (literal (valuationOf q) (740)) (literal (valuationOf q) (742)) (countLit q [-26]) (countLit q [-27, -30]) (count742 q) 1 (meaning740 q) (meaning742 q) hs
  change valuationOf q 740 = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 740 = false ∨ valuation q 742 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 741 = false ∨ valuationOf q 744 = true := by
  have hs : count742 q = (countLit q [-26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (741)) (literal (valuationOf q) (744)) (countLit q [-26]) (countLit q [-27, -30]) (count742 q) 1 2 (meaningNeg26 q) (meaning741 q) (meaning744 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 741 = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 741 = false ∨ valuation q 744 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (745)) (countLit q [-34]) (countLit q [-35]) (count745 q) 1 (meaningNeg34 q) (meaning745 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 745 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 747 = true := by
  have hs : count747 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (745)) (literal (valuationOf q) (747)) (countLit q [-32]) (countLit q [-34, -35]) (count747 q) 1 (meaning745 q) (meaning747 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 747 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 742 = false ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-26, -27, -30]) + (countLit q [-32, -34, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -27, -30]) (l₂ := [-32, -34, -35])
  have hm := merge_left (literal (valuationOf q) (742)) (literal (valuationOf q) (750)) (countLit q [-26, -27, -30]) (countLit q [-32, -34, -35]) (count750 q) 1 (meaning742 q) (meaning750 q) hs
  change valuationOf q 742 = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 742 = false ∨ valuation q 750 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E094.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112094
