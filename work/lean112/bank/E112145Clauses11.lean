import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning175 q) (meaning337 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 337 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174, 175])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [173]) (countLit q [174, 175]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174, 175])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (339)) (countLit q [173]) (countLit q [174, 175]) (count339 q) 1 (meaning173 q) (meaning339 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 339 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (341)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175]) (count341 q) 1 (meaning335 q) (meaning341 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 341 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175]) (count341 q) 1 1 (meaning335 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning178 q) (meaning343 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 343 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [176]) (countLit q [177, 178]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_right (literal (valuationOf q) (180)) (literal (valuationOf q) (347)) (countLit q [179]) (countLit q [180]) (count347 q) 1 (meaning180 q) (meaning347 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 347 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (349)) (countLit q [181]) (countLit q [182]) (count349 q) 1 (meaning181 q) (meaning349 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 349 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [179, 180]) (countLit q [181, 182]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (351)) (countLit q [179, 180]) (countLit q [181, 182]) (count351 q) 1 (meaning347 q) (meaning351 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 351 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (353)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count353 q) 1 (meaning345 q) (meaning353 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 353 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (355)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 (meaning341 q) (meaning355 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 355 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_two (literal (valuationOf q) (341)) (literal (valuationOf q) (353)) (literal (valuationOf q) (356)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 1 (meaning341 q) (meaning353 q) (meaning356 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 353 = false ∨ valuation q 356 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (342)) (literal (valuationOf q) (356)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 2 (meaning342 q) (meaning356 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 356 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 356 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (356)) (literal (valuationOf q) (358)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 2 (meaning356 q) (meaning358 q) hs
  change valuationOf q 356 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 358 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (357)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning331 q) (meaning357 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 357 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 332 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (332)) (literal (valuationOf q) (358)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 2 (meaning332 q) (meaning358 q) hs
  change valuationOf q 332 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 332 = false ∨ valuation q 358 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (361)) (countLit q [183]) (countLit q [184, 185]) (count361 q) 1 (meaning183 q) (meaning361 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 361 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning188 q) (meaning363 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 363 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning187 q) (meaning363 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 363 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (367)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188]) (count367 q) 1 (meaning361 q) (meaning367 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 367 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (369)) (countLit q [190]) (countLit q [191]) (count369 q) 1 (meaning190 q) (meaning369 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 369 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_two (literal (valuationOf q) (189)) (literal (valuationOf q) (369)) (literal (valuationOf q) (372)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 1 (meaning189 q) (meaning369 q) (meaning372 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 369 = false ∨ valuation q 372 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E145.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112145
