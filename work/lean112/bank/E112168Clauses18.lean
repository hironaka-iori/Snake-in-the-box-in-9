import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (333)) (countLit q [157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning319 q) (meaning333 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 333 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (335)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 1 (meaning307 q) (meaning335 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 335 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (337)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count337 q) 1 (meaning281 q) (meaning337 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 337 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 335 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (335)) (literal (valuationOf q) (338)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count337 q) 1 1 (meaning281 q) (meaning335 q) (meaning338 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 335 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 335 = false ∨ valuation q 338 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (338)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count337 q) 2 (meaning282 q) (meaning338 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 338 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_right (literal (valuationOf q) (173)) (literal (valuationOf q) (339)) (countLit q [172]) (countLit q [173]) (count339 q) 1 (meaning173 q) (meaning339 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 339 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [171]) (countLit q [172, 173]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_right (literal (valuationOf q) (177)) (literal (valuationOf q) (345)) (countLit q [176]) (countLit q [177]) (count345 q) 1 (meaning177 q) (meaning345 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 345 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [174, 175]) (countLit q [176, 177]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [171, 172, 173]) (countLit q [174, 175, 176, 177]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (349)) (countLit q [171, 172, 173]) (countLit q [174, 175, 176, 177]) (count349 q) 1 (meaning341 q) (meaning349 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 349 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (351)) (countLit q [179]) (countLit q [180]) (count351 q) 1 (meaning179 q) (meaning351 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 351 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179, 180])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [178]) (countLit q [179, 180]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (353)) (countLit q [178]) (countLit q [179, 180]) (count353 q) 1 (meaning178 q) (meaning353 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 353 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (355)) (countLit q [181]) (countLit q [182]) (count355 q) 1 (meaning181 q) (meaning355 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 355 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_right (literal (valuationOf q) (185)) (literal (valuationOf q) (357)) (countLit q [184]) (countLit q [185]) (count357 q) 1 (meaning185 q) (meaning357 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 357 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [184, 185]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [184, 185]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 184, 185]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 184, 185])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [178, 179, 180]) (countLit q [181, 182, 184, 185]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 184, 185]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 184, 185])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (361)) (countLit q [178, 179, 180]) (countLit q [181, 182, 184, 185]) (count361 q) 1 (meaning353 q) (meaning361 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 361 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 184, 185]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 184, 185])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 184, 185]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 184, 185]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 184, 185])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (363)) (countLit q [171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 184, 185]) (count363 q) 1 (meaning349 q) (meaning363 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 363 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning188 q) (meaning365 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 365 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning187 q) (meaning365 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 365 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [186]) (countLit q [187, 188]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (369)) (countLit q [189]) (countLit q [190]) (count369 q) 1 (meaning189 q) (meaning369 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 369 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [189, 190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [189, 190]) (l₂ := [191, 192])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (373)) (countLit q [189, 190]) (countLit q [191, 192]) (count373 q) 1 (meaning369 q) (meaning373 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 373 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E168.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112168
