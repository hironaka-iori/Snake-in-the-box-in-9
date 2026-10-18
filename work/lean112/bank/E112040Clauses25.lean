import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_left (literal (valuationOf q) (185)) (literal (valuationOf q) (363)) (countLit q [185]) (countLit q [186]) (count363 q) 1 (meaning185 q) (meaning363 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 363 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [183, 184]) (countLit q [185, 186]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [180, 181, 182]) + (countLit q [183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182]) (l₂ := [183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [180, 181, 182]) (countLit q [183, 184, 185, 186]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [180, 181, 182]) + (countLit q [183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182]) (l₂ := [183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (367)) (countLit q [180, 181, 182]) (countLit q [183, 184, 185, 186]) (count367 q) 1 (meaning359 q) (meaning367 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 367 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (369)) (countLit q [187]) (countLit q [188]) (count369 q) 1 (meaning187 q) (meaning369 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 369 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [187, 188]) (countLit q [189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (373)) (countLit q [187, 188]) (countLit q [189, 190]) (count373 q) 1 (meaning369 q) (meaning373 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 373 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_right (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [191, 192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [191, 192]) (l₂ := [193, 194])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (379)) (countLit q [191, 192]) (countLit q [193, 194]) (count379 q) 1 (meaning375 q) (meaning379 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 379 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [187, 188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [187, 188, 189, 190]) (countLit q [191, 192, 193, 194]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [187, 188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (381)) (countLit q [187, 188, 189, 190]) (countLit q [191, 192, 193, 194]) (count381 q) 1 (meaning373 q) (meaning381 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 381 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (383)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 1 (meaning367 q) (meaning383 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 383 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 381 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (381)) (literal (valuationOf q) (384)) (countLit q [180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194]) (count383 q) 1 1 (meaning367 q) (meaning381 q) (meaning384 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 381 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 381 = false ∨ valuation q 384 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196, 197])
  have hm := merge_left (literal (valuationOf q) (195)) (literal (valuationOf q) (387)) (countLit q [195]) (countLit q [196, 197]) (count387 q) 1 (meaning195 q) (meaning387 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 387 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (395)) (countLit q [195, 196, 197]) (countLit q [198, 199, 200, 201]) (count395 q) 1 (meaning387 q) (meaning395 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 395 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 204 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_left (literal (valuationOf q) (204)) (literal (valuationOf q) (399)) (countLit q [204]) (countLit q [205]) (count399 q) 1 (meaning204 q) (meaning399 q) hs
  change valuationOf q 204 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 204 = false ∨ valuation q 399 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (403)) (countLit q [206]) (countLit q [207]) (count403 q) 1 (meaning206 q) (meaning403 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 403 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (405)) (countLit q [208]) (countLit q [209]) (count405 q) 1 (meaning209 q) (meaning405 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 405 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (405)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning405 q) (meaning407 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 407 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [206, 207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [206, 207]) (l₂ := [208, 209])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (407)) (countLit q [206, 207]) (countLit q [208, 209]) (count407 q) 1 (meaning403 q) (meaning407 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 407 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [202, 203, 204, 205]) + (countLit q [206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [202, 203, 204, 205]) (l₂ := [206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (401)) (literal (valuationOf q) (409)) (countLit q [202, 203, 204, 205]) (countLit q [206, 207, 208, 209]) (count409 q) 1 (meaning401 q) (meaning409 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 409 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (409)) (literal (valuationOf q) (411)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (count411 q) 1 (meaning409 q) (meaning411 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 411 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 411 = true := by
  have hs : count411 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (395)) (literal (valuationOf q) (411)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (count411 q) 1 (meaning395 q) (meaning411 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 411 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_two (literal (valuationOf q) (395)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208, 209]) (count411 q) 1 1 (meaning395 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 411 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (411)) (literal (valuationOf q) (413)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (count413 q) 1 (meaning411 q) (meaning413 q) hs
  change valuationOf q 411 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 411 = false ∨ valuation q 413 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 412 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_right (literal (valuationOf q) (412)) (literal (valuationOf q) (414)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (count413 q) 2 (meaning412 q) (meaning414 q) hs
  change valuationOf q 412 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 412 = false ∨ valuation q 414 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (413)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (count413 q) 1 (meaning383 q) (meaning413 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 413 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true := by
  have hs : count413 q = (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209])
  have hm := merge_two (literal (valuationOf q) (383)) (literal (valuationOf q) (411)) (literal (valuationOf q) (414)) (countLit q [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209]) (count413 q) 1 1 (meaning383 q) (meaning411 q) (meaning414 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 411 = false ∨ valuationOf q 414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 411 = false ∨ valuation q 414 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E040.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112040
