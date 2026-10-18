import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning208 q) (meaning405 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 405 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning403 q) (meaning407 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 407 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning401 q) (meaning409 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 409 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_two (literal (valuationOf q) (401)) (literal (valuationOf q) (407)) (literal (valuationOf q) (410)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 1 (meaning401 q) (meaning407 q) (meaning410 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 407 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 407 = false ∨ valuation q 410 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning213 q) (meaning413 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 413 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [210, 211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [210, 211, 212, 213]) + (countLit q [214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [210, 211, 212, 213]) (l₂ := [214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (415)) (literal (valuationOf q) (423)) (countLit q [210, 211, 212, 213]) (countLit q [214, 215, 216, 217]) (count423 q) 1 (meaning415 q) (meaning423 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 423 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (423)) (literal (valuationOf q) (425)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning423 q) (meaning425 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 425 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (425)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 1 (meaning409 q) (meaning425 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 425 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 426 = true := by
  have hs : count425 q = (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) + (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205, 206, 207, 208, 209]) (l₂ := [210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (410)) (literal (valuationOf q) (426)) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (countLit q [210, 211, 212, 213, 214, 215, 216, 217]) (count425 q) 2 (meaning410 q) (meaning426 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 426 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 426 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_right (literal (valuationOf q) (426)) (literal (valuationOf q) (428)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 2 (meaning426 q) (meaning428 q) hs
  change valuationOf q 426 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 426 = false ∨ valuation q 428 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (427)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 1 (meaning395 q) (meaning427 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 427 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (425)) (literal (valuationOf q) (428)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 1 1 (meaning395 q) (meaning425 q) (meaning428 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 425 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 425 = false ∨ valuation q 428 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 396 = false ∨ valuationOf q 428 = true := by
  have hs : count427 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217])
  have hm := merge_left (literal (valuationOf q) (396)) (literal (valuationOf q) (428)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (count427 q) 2 (meaning396 q) (meaning428 q) hs
  change valuationOf q 396 = false ∨ valuationOf q 428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 396 = false ∨ valuation q 428 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [219]) + (countLit q [220]) := List.countP_append (p := literal q) (l₁ := [219]) (l₂ := [220])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (429)) (countLit q [219]) (countLit q [220]) (count429 q) 1 (meaning219 q) (meaning429 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 429 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [218]) (l₂ := [219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [218]) (countLit q [219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_right (literal (valuationOf q) (222)) (literal (valuationOf q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning222 q) (meaning433 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 433 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (433)) (countLit q [221]) (countLit q [222]) (count433 q) 1 (meaning221 q) (meaning433 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 433 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 222 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [221]) + (countLit q [222]) := List.countP_append (p := literal q) (l₁ := [221]) (l₂ := [222])
  have hm := merge_two (literal (valuationOf q) (221)) (literal (valuationOf q) (222)) (literal (valuationOf q) (434)) (countLit q [221]) (countLit q [222]) (count433 q) 1 1 (meaning221 q) (meaning222 q) (meaning434 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 222 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 222 = false ∨ valuation q 434 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 433 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (433)) (literal (valuationOf q) (437)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 1 (meaning433 q) (meaning437 q) hs
  change valuationOf q 433 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 433 = false ∨ valuation q 437 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 434 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [221, 222]) + (countLit q [223, 224]) := List.countP_append (p := literal q) (l₁ := [221, 222]) (l₂ := [223, 224])
  have hm := merge_left (literal (valuationOf q) (434)) (literal (valuationOf q) (438)) (countLit q [221, 222]) (countLit q [223, 224]) (count437 q) 2 (meaning434 q) (meaning438 q) hs
  change valuationOf q 434 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 434 = false ∨ valuation q 438 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (437)) (literal (valuationOf q) (439)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 (meaning437 q) (meaning439 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 439 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_right (literal (valuationOf q) (438)) (literal (valuationOf q) (440)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 2 (meaning438 q) (meaning440 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 440 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [218, 219, 220]) + (countLit q [221, 222, 223, 224]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220]) (l₂ := [221, 222, 223, 224])
  have hm := merge_two (literal (valuationOf q) (431)) (literal (valuationOf q) (437)) (literal (valuationOf q) (440)) (countLit q [218, 219, 220]) (countLit q [221, 222, 223, 224]) (count439 q) 1 1 (meaning431 q) (meaning437 q) (meaning440 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 437 = false ∨ valuation q 440 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [227]) + (countLit q [228]) := List.countP_append (p := literal q) (l₁ := [227]) (l₂ := [228])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (443)) (countLit q [227]) (countLit q [228]) (count443 q) 1 (meaning228 q) (meaning443 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 443 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [225, 226]) (countLit q [227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [229]) + (countLit q [230]) := List.countP_append (p := literal q) (l₁ := [229]) (l₂ := [230])
  have hm := merge_right (literal (valuationOf q) (230)) (literal (valuationOf q) (447)) (countLit q [229]) (countLit q [230]) (count447 q) 1 (meaning230 q) (meaning447 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 447 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [229, 230]) + (countLit q [231, 232]) := List.countP_append (p := literal q) (l₁ := [229, 230]) (l₂ := [231, 232])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (451)) (countLit q [229, 230]) (countLit q [231, 232]) (count451 q) 1 (meaning447 q) (meaning451 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 451 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E153.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112153
