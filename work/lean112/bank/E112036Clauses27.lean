import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (331)) (countLit q [168]) (countLit q [169]) (count331 q) 1 (meaning168 q) (meaning331 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 331 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (333)) (countLit q [170]) (countLit q [171]) (count333 q) 1 (meaning170 q) (meaning333 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 333 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [168, 169]) (countLit q [170, 171]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (335)) (countLit q [168, 169]) (countLit q [170, 171]) (count335 q) 1 (meaning331 q) (meaning335 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 335 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [168, 169, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (343)) (countLit q [168, 169, 170, 171]) (countLit q [172, 173, 174, 175]) (count343 q) 1 (meaning335 q) (meaning343 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 343 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_right (literal (valuationOf q) (177)) (literal (valuationOf q) (347)) (countLit q [176]) (countLit q [177]) (count347 q) 1 (meaning177 q) (meaning347 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 347 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (347)) (countLit q [176]) (countLit q [177]) (count347 q) 1 (meaning176 q) (meaning347 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 347 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 177 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_two (literal (valuationOf q) (176)) (literal (valuationOf q) (177)) (literal (valuationOf q) (348)) (countLit q [176]) (countLit q [177]) (count347 q) 1 1 (meaning176 q) (meaning177 q) (meaning348 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 177 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 177 = false ∨ valuation q 348 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_right (literal (valuationOf q) (179)) (literal (valuationOf q) (349)) (countLit q [178]) (countLit q [179]) (count349 q) 1 (meaning179 q) (meaning349 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 349 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [176, 177]) (countLit q [178, 179]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (351)) (countLit q [176, 177]) (countLit q [178, 179]) (count351 q) 1 (meaning347 q) (meaning351 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 351 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (352)) (countLit q [176, 177]) (countLit q [178, 179]) (count351 q) 2 (meaning348 q) (meaning352 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 352 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_right (literal (valuationOf q) (181)) (literal (valuationOf q) (353)) (countLit q [180]) (countLit q [181]) (count353 q) 1 (meaning181 q) (meaning353 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 353 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (357)) (countLit q [180, 181]) (countLit q [182, 183]) (count357 q) 1 (meaning353 q) (meaning357 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 357 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (359)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 1 (meaning351 q) (meaning359 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 359 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 352 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (352)) (literal (valuationOf q) (360)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 2 (meaning352 q) (meaning360 q) hs
  change valuationOf q 352 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 352 = false ∨ valuation q 360 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuationOf q) (188)) (literal (valuationOf q) (367)) (countLit q [188]) (countLit q [189]) (count367 q) 1 (meaning188 q) (meaning367 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 367 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (369)) (countLit q [190]) (countLit q [191]) (count369 q) 1 (meaning190 q) (meaning369 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 369 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [188, 189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [188, 189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [188, 189]) (countLit q [190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [188, 189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [188, 189]) (l₂ := [190, 191])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (371)) (countLit q [188, 189]) (countLit q [190, 191]) (count371 q) 1 (meaning367 q) (meaning371 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 371 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [184, 185, 186, 187]) + (countLit q [188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186, 187]) (l₂ := [188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [184, 185, 186, 187]) (countLit q [188, 189, 190, 191]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (375)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning359 q) (meaning375 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 375 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (373)) (literal (valuationOf q) (376)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 1 (meaning359 q) (meaning373 q) (meaning376 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 373 = false ∨ valuation q 376 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (376)) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190, 191]) (count375 q) 2 (meaning360 q) (meaning376 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 376 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (376)) (literal (valuationOf q) (378)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count377 q) 2 (meaning376 q) (meaning378 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 378 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (377)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count377 q) 1 (meaning345 q) (meaning377 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 377 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_two (literal (valuationOf q) (345)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count377 q) 1 1 (meaning345 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E036.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112036
