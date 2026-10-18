import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [206, 207, 208]) (countLit q [209, 210, 211, 212]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 412 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (412)) (literal (valuationOf q) (414)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 2 (meaning412 q) (meaning414 q) hs
  change valuationOf q 412 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 412 = false ∨ valuation q 414 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (413)) (countLit q [199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212]) (count413 q) 1 (meaning399 q) (meaning413 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 413 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 414 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (414)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning414 q) (meaning416 q) hs
  change valuationOf q 414 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 414 = false ∨ valuation q 416 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (415)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning387 q) (meaning415 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 415 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (416)) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning388 q) (meaning416 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 416 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (416)) (literal (valuationOf q) (418)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning416 q) (meaning418 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 418 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (417)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning363 q) (meaning417 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 417 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (363)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 1 (meaning363 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 364 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (364)) (literal (valuationOf q) (418)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning364 q) (meaning418 q) hs
  change valuationOf q 364 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 364 = false ∨ valuation q 418 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (418)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning418 q) (meaning420 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 420 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (417)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 1 1 (meaning313 q) (meaning417 q) (meaning420 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 417 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 417 = false ∨ valuation q 420 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 420 = true := by
  have hs : count419 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (314)) (literal (valuationOf q) (420)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count419 q) 2 (meaning314 q) (meaning420 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 420 = true := counterClause241 (baseVal q)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 420 = false := by
  rw [value420]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count419 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause243 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1285)) (countLit q [-5]) (countLit q [-7]) (count1285 q) 1 (meaningNeg7 q) (meaning1285 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1285 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1285 = true := by
  have hs : count1285 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1285)) (countLit q [-5]) (countLit q [-7]) (count1285 q) 1 (meaningNeg5 q) (meaning1285 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1285 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1285 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 1285 = false ∨ valuationOf q 1287 = true := by
  have hs : count1287 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1285)) (literal (valuationOf q) (1287)) (countLit q [-2]) (countLit q [-5, -7]) (count1287 q) 1 (meaning1285 q) (meaning1287 q) hs
  change valuationOf q 1285 = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 1285 = false ∨ valuation q 1287 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1287 = true := by
  have hs : count1287 q = (countLit q [-2]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1287)) (countLit q [-2]) (countLit q [-5, -7]) (count1287 q) 1 (meaningNeg2 q) (meaning1287 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1287 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1287 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1290)) (countLit q [-12]) (countLit q [-13]) (count1290 q) 1 (meaningNeg13 q) (meaning1290 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1290 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1290 = true := by
  have hs : count1290 q = (countLit q [-12]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1290)) (countLit q [-12]) (countLit q [-13]) (count1290 q) 1 (meaningNeg12 q) (meaning1290 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1290 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 1290 = false ∨ valuationOf q 1292 = true := by
  have hs : count1292 q = (countLit q [-11]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1290)) (literal (valuationOf q) (1292)) (countLit q [-11]) (countLit q [-12, -13]) (count1292 q) 1 (meaning1290 q) (meaning1292 q) hs
  change valuationOf q 1290 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 1290 = false ∨ valuation q 1292 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1292 = true := by
  have hs : count1292 q = (countLit q [-11]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1292)) (countLit q [-11]) (countLit q [-12, -13]) (count1292 q) 1 (meaningNeg11 q) (meaning1292 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1292 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 1292 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-2, -5, -7]) + (countLit q [-11, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-11, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1292)) (literal (valuationOf q) (1295)) (countLit q [-2, -5, -7]) (countLit q [-11, -12, -13]) (count1295 q) 1 (meaning1292 q) (meaning1295 q) hs
  change valuationOf q 1292 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 1292 = false ∨ valuation q 1295 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 1287 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-2, -5, -7]) + (countLit q [-11, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-11, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1287)) (literal (valuationOf q) (1295)) (countLit q [-2, -5, -7]) (countLit q [-11, -12, -13]) (count1295 q) 1 (meaning1287 q) (meaning1295 q) hs
  change valuationOf q 1287 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 1287 = false ∨ valuation q 1295 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 1287 = false ∨ valuationOf q 1292 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-2, -5, -7]) + (countLit q [-11, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-11, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1287)) (literal (valuationOf q) (1292)) (literal (valuationOf q) (1296)) (countLit q [-2, -5, -7]) (countLit q [-11, -12, -13]) (count1295 q) 1 1 (meaning1287 q) (meaning1292 q) (meaning1296 q) hs
  change valuationOf q 1287 = false ∨ valuationOf q 1292 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 1287 = false ∨ valuation q 1292 = false ∨ valuation q 1296 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-18]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1301)) (countLit q [-18]) (countLit q [-20]) (count1301 q) 1 (meaningNeg18 q) (meaning1301 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1301 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-14]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18, -20])
  have hm := merge_right (literal (valuationOf q) (1301)) (literal (valuationOf q) (1303)) (countLit q [-14]) (countLit q [-18, -20]) (count1303 q) 1 (meaning1301 q) (meaning1303 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1303 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-14]) + (countLit q [-18, -20]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18, -20])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1303)) (countLit q [-14]) (countLit q [-18, -20]) (count1303 q) 1 (meaningNeg14 q) (meaning1303 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1303 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E249.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112249
