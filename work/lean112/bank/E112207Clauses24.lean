import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (343)) (countLit q [161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) (count343 q) 1 (meaning327 q) (meaning343 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 343 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_two (literal (valuationOf q) (327)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) (count343 q) 1 1 (meaning327 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (328)) (literal (valuationOf q) (344)) (countLit q [161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) (count343 q) 2 (meaning328 q) (meaning344 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 344 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (344)) (literal (valuationOf q) (346)) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count345 q) 2 (meaning344 q) (meaning346 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 346 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (345)) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count345 q) 1 (meaning315 q) (meaning345 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 345 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_two (literal (valuationOf q) (315)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count345 q) 1 1 (meaning315 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 316 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (316)) (literal (valuationOf q) (346)) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count345 q) 2 (meaning316 q) (meaning346 q) hs
  change valuationOf q 316 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 316 = false ∨ valuation q 346 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (347)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count347 q) 1 (meaning289 q) (meaning347 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 347 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count347 q) 1 1 (meaning289 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (290)) (literal (valuationOf q) (348)) (countLit q [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (count347 q) 2 (meaning290 q) (meaning348 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 348 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (349)) (countLit q [177]) (countLit q [178]) (count349 q) 1 (meaning177 q) (meaning349 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 349 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [176]) (countLit q [177, 178]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_right (literal (valuationOf q) (180)) (literal (valuationOf q) (353)) (countLit q [179]) (countLit q [180]) (count353 q) 1 (meaning180 q) (meaning353 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 353 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (353)) (countLit q [179]) (countLit q [180]) (count353 q) 1 (meaning179 q) (meaning353 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 353 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 180 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_two (literal (valuationOf q) (179)) (literal (valuationOf q) (180)) (literal (valuationOf q) (354)) (countLit q [179]) (countLit q [180]) (count353 q) 1 1 (meaning179 q) (meaning180 q) (meaning354 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 180 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 180 = false ∨ valuation q 354 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (357)) (countLit q [179, 180]) (countLit q [181, 182]) (count357 q) 1 (meaning353 q) (meaning357 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 357 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (358)) (countLit q [179, 180]) (countLit q [181, 182]) (count357 q) 2 (meaning354 q) (meaning358 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 358 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 358 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (358)) (literal (valuationOf q) (360)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count359 q) 2 (meaning358 q) (meaning360 q) hs
  change valuationOf q 358 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 360 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (359)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count359 q) 1 (meaning351 q) (meaning359 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 359 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_two (literal (valuationOf q) (351)) (literal (valuationOf q) (357)) (literal (valuationOf q) (360)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count359 q) 1 1 (meaning351 q) (meaning357 q) (meaning360 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 357 = false ∨ valuation q 360 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (363)) (countLit q [183]) (countLit q [184, 185]) (count363 q) 1 (meaning183 q) (meaning363 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 363 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [186]) + (countLit q [187]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (365)) (countLit q [186]) (countLit q [187]) (count365 q) 1 (meaning186 q) (meaning365 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 365 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_right (literal (valuationOf q) (189)) (literal (valuationOf q) (367)) (countLit q [188]) (countLit q [189]) (count367 q) 1 (meaning189 q) (meaning367 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 367 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuationOf q) (188)) (literal (valuationOf q) (367)) (countLit q [188]) (countLit q [189]) (count367 q) 1 (meaning188 q) (meaning367 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 367 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 189 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_two (literal (valuationOf q) (188)) (literal (valuationOf q) (189)) (literal (valuationOf q) (368)) (countLit q [188]) (countLit q [189]) (count367 q) 1 1 (meaning188 q) (meaning189 q) (meaning368 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 189 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 189 = false ∨ valuation q 368 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [186, 187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [186, 187]) (l₂ := [188, 189])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [186, 187]) (countLit q [188, 189]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [186, 187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [186, 187]) (l₂ := [188, 189])
  have hm := merge_right (literal (valuationOf q) (368)) (literal (valuationOf q) (370)) (countLit q [186, 187]) (countLit q [188, 189]) (count369 q) 2 (meaning368 q) (meaning370 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 370 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [186, 187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [186, 187]) (l₂ := [188, 189])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (369)) (countLit q [186, 187]) (countLit q [188, 189]) (count369 q) 1 (meaning365 q) (meaning369 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 369 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E207.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112207
