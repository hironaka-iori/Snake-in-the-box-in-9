import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [211]) + (countLit q [212]) := List.countP_append (p := literal q) (l₁ := [211]) (l₂ := [212])
  have hm := merge_right (literal (valuationOf q) (212)) (literal (valuationOf q) (409)) (countLit q [211]) (countLit q [212]) (count409 q) 1 (meaning212 q) (meaning409 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 409 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [209, 210]) (countLit q [211, 212]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (411)) (countLit q [209, 210]) (countLit q [211, 212]) (count411 q) 1 (meaning407 q) (meaning411 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 411 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_two (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [209, 210]) (countLit q [211, 212]) (count411 q) 1 1 (meaning407 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [205, 206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [205, 206, 207, 208]) (countLit q [209, 210, 211, 212]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 412 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [205, 206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (412)) (literal (valuationOf q) (414)) (countLit q [205, 206, 207, 208]) (countLit q [209, 210, 211, 212]) (count413 q) 2 (meaning412 q) (meaning414 q) hs
  change valuationOf q 412 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 412 = false ∨ valuation q 414 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [205, 206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (413)) (countLit q [205, 206, 207, 208]) (countLit q [209, 210, 211, 212]) (count413 q) 1 (meaning405 q) (meaning413 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 413 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [205, 206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (411)) (literal (valuationOf q) (414)) (countLit q [205, 206, 207, 208]) (countLit q [209, 210, 211, 212]) (count413 q) 1 1 (meaning405 q) (meaning411 q) (meaning414 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 411 = false ∨ valuation q 414 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [205, 206, 207, 208]) + (countLit q [209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [205, 206, 207, 208]) (l₂ := [209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (414)) (countLit q [205, 206, 207, 208]) (countLit q [209, 210, 211, 212]) (count413 q) 2 (meaning406 q) (meaning414 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 414 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 414 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (414)) (literal (valuationOf q) (416)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning414 q) (meaning416 q) hs
  change valuationOf q 414 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 414 = false ∨ valuation q 416 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (399)) (literal (valuationOf q) (415)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 (meaning399 q) (meaning415 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 415 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (399)) (literal (valuationOf q) (413)) (literal (valuationOf q) (416)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 1 1 (meaning399 q) (meaning413 q) (meaning416 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 413 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 413 = false ∨ valuation q 416 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 400 = false ∨ valuationOf q 416 = true := by
  have hs : count415 q = (countLit q [198, 199, 200, 201, 202, 203, 204]) + (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [198, 199, 200, 201, 202, 203, 204]) (l₂ := [205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (400)) (literal (valuationOf q) (416)) (countLit q [198, 199, 200, 201, 202, 203, 204]) (countLit q [205, 206, 207, 208, 209, 210, 211, 212]) (count415 q) 2 (meaning400 q) (meaning416 q) hs
  change valuationOf q 400 = false ∨ valuationOf q 416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 400 = false ∨ valuation q 416 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 416 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_right (literal (valuationOf q) (416)) (literal (valuationOf q) (418)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning416 q) (meaning418 q) hs
  change valuationOf q 416 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 416 = false ∨ valuation q 418 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (417)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 (meaning387 q) (meaning417 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 417 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 1 1 (meaning387 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) + (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (l₂ := [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (418)) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]) (countLit q [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]) (count417 q) 2 (meaning388 q) (meaning418 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 418 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [213]) (l₂ := [214, 215])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (421)) (countLit q [213]) (countLit q [214, 215]) (count421 q) 1 (meaning213 q) (meaning421 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 421 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 216 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [216]) + (countLit q [217]) := List.countP_append (p := literal q) (l₁ := [216]) (l₂ := [217])
  have hm := merge_left (literal (valuationOf q) (216)) (literal (valuationOf q) (423)) (countLit q [216]) (countLit q [217]) (count423 q) 1 (meaning216 q) (meaning423 q) hs
  change valuationOf q 216 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 423 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [218]) + (countLit q [219]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (425)) (countLit q [218]) (countLit q [219]) (count425 q) 1 (meaning219 q) (meaning425 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 425 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [216, 217]) + (countLit q [218, 219]) := List.countP_append (p := literal q) (l₁ := [216, 217]) (l₂ := [218, 219])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [216, 217]) (countLit q [218, 219]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [216, 217]) + (countLit q [218, 219]) := List.countP_append (p := literal q) (l₁ := [216, 217]) (l₂ := [218, 219])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (427)) (countLit q [216, 217]) (countLit q [218, 219]) (count427 q) 1 (meaning423 q) (meaning427 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 427 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [216, 217]) + (countLit q [218, 219]) := List.countP_append (p := literal q) (l₁ := [216, 217]) (l₂ := [218, 219])
  have hm := merge_two (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [216, 217]) (countLit q [218, 219]) (count427 q) 1 1 (meaning423 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [213, 214, 215]) + (countLit q [216, 217, 218, 219]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215]) (l₂ := [216, 217, 218, 219])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [213, 214, 215]) (countLit q [216, 217, 218, 219]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [213, 214, 215]) + (countLit q [216, 217, 218, 219]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215]) (l₂ := [216, 217, 218, 219])
  have hm := merge_right (literal (valuationOf q) (428)) (literal (valuationOf q) (430)) (countLit q [213, 214, 215]) (countLit q [216, 217, 218, 219]) (count429 q) 2 (meaning428 q) (meaning430 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 430 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [213, 214, 215]) + (countLit q [216, 217, 218, 219]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215]) (l₂ := [216, 217, 218, 219])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (429)) (countLit q [213, 214, 215]) (countLit q [216, 217, 218, 219]) (count429 q) 1 (meaning421 q) (meaning429 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 429 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true := by
  have hs : count429 q = (countLit q [213, 214, 215]) + (countLit q [216, 217, 218, 219]) := List.countP_append (p := literal q) (l₁ := [213, 214, 215]) (l₂ := [216, 217, 218, 219])
  have hm := merge_two (literal (valuationOf q) (421)) (literal (valuationOf q) (427)) (literal (valuationOf q) (430)) (countLit q [213, 214, 215]) (countLit q [216, 217, 218, 219]) (count429 q) 1 1 (meaning421 q) (meaning427 q) (meaning430 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 427 = false ∨ valuationOf q 430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 427 = false ∨ valuation q 430 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_left (literal (valuationOf q) (220)) (literal (valuationOf q) (431)) (countLit q [220]) (countLit q [221]) (count431 q) 1 (meaning220 q) (meaning431 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 431 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [222]) + (countLit q [223]) := List.countP_append (p := literal q) (l₁ := [222]) (l₂ := [223])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (433)) (countLit q [222]) (countLit q [223]) (count433 q) 1 (meaning223 q) (meaning433 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 433 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [220, 221]) + (countLit q [222, 223]) := List.countP_append (p := literal q) (l₁ := [220, 221]) (l₂ := [222, 223])
  have hm := merge_right (literal (valuationOf q) (433)) (literal (valuationOf q) (435)) (countLit q [220, 221]) (countLit q [222, 223]) (count435 q) 1 (meaning433 q) (meaning435 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 435 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E019.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112019
