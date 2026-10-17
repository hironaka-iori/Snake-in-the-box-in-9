import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [211]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (407)) (countLit q [211]) (countLit q [212]) (count407 q) 1 (meaning211 q) (meaning407 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 407 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (409)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 1 (meaning405 q) (meaning409 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 409 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (411)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 1 (meaning403 q) (meaning411 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 411 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (412)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 2 (meaning404 q) (meaning412 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 412 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 412 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (412)) (literal (valuationOf q) (414)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 2 (meaning412 q) (meaning414 q) hs
  change valuationOf q 412 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 412 = false ∨ valuation q 414 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning399 q) (meaning413 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 413 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (411)) (literal (valuationOf q) (414)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 1 (meaning399 q) (meaning411 q) (meaning414 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 411 = false ∨ valuation q 414 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (414)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 2 (meaning400 q) (meaning414 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 414 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 414 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (414)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning414 q) (meaning416 q) hs
  change valuationOf q 414 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 414 = false ∨ valuation q 416 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (415)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning387 q) (meaning415 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 415 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (413)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 1 (meaning387 q) (meaning413 q) (meaning416 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 413 = false ∨ valuation q 416 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning388 q) (meaning416 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 416 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (416)) (literal (valuationOf q) (418)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning416 q) (meaning418 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 418 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (417)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning363 q) (meaning417 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 417 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (363)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 1 (meaning363 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 364 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (364)) (literal (valuationOf q) (418)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning364 q) (meaning418 q) hs
  change valuationOf q 364 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 364 = false ∨ valuation q 418 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (418)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (417)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 1 1 (meaning313 q) (meaning417 q) (meaning420 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 417 = false ∨ valuation q 420 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (314)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning314 q) (meaning420 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 420 = true := counterClause568 (baseVal q)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 420 = false := by
  rw [value420]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count419 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true := by
  rw [value107, value108, value109, value110, value111, value112, value113, value114, value115, value116, value117, value118, value119, value120, value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause571 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1252)) (countLit q [-4]) (countLit q [-7]) (count1252 q) 1 (meaningNeg7 q) (meaning1252 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1252 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1252 = true := by
  have hs : count1252 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1252)) (countLit q [-4]) (countLit q [-7]) (count1252 q) 1 (meaningNeg4 q) (meaning1252 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1252 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1253 = true := by
  have hs : count1252 q = (countLit q [-4]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1253)) (countLit q [-4]) (countLit q [-7]) (count1252 q) 1 1 (meaningNeg4 q) (meaningNeg7 q) (meaning1253 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 7 = true ∨ valuation q 1253 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1252 = false ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_right (literal (valuationOf q) (1252)) (literal (valuationOf q) (1254)) (countLit q [-2]) (countLit q [-4, -7]) (count1254 q) 1 (meaning1252 q) (meaning1254 q) hs
  change valuationOf q 1252 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1252 = false ∨ valuation q 1254 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1255 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_right (literal (valuationOf q) (1253)) (literal (valuationOf q) (1255)) (countLit q [-2]) (countLit q [-4, -7]) (count1254 q) 2 (meaning1253 q) (meaning1255 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1255 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1254 = true := by
  have hs : count1254 q = (countLit q [-2]) + (countLit q [-4, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1254)) (countLit q [-2]) (countLit q [-4, -7]) (count1254 q) 1 (meaningNeg2 q) (meaning1254 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1254 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E091.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112091
