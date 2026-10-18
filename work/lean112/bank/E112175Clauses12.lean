import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174, 175])
  have hm := merge_right (literal (valuationOf q) (338)) (literal (valuationOf q) (340)) (countLit q [173]) (countLit q [174, 175]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (341)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175]) (count341 q) 1 (meaning335 q) (meaning341 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 341 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (347)) (countLit q [179]) (countLit q [180]) (count347 q) 1 (meaning179 q) (meaning347 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 347 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (349)) (countLit q [181]) (countLit q [182]) (count349 q) 1 (meaning181 q) (meaning349 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 349 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [179, 180]) (countLit q [181, 182]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (literal (valuationOf q) (352)) (countLit q [179, 180]) (countLit q [181, 182]) (count351 q) 1 1 (meaning347 q) (meaning349 q) (meaning352 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = false ∨ valuation q 352 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 352 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (352)) (literal (valuationOf q) (354)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count353 q) 2 (meaning352 q) (meaning354 q) hs
  change valuationOf q 352 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 352 = false ∨ valuation q 354 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (354)) (literal (valuationOf q) (356)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 2 (meaning354 q) (meaning356 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 356 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (355)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 1 (meaning341 q) (meaning355 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 355 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (342)) (literal (valuationOf q) (356)) (countLit q [170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182]) (count355 q) 2 (meaning342 q) (meaning356 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 356 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 356 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (356)) (literal (valuationOf q) (358)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 2 (meaning356 q) (meaning358 q) hs
  change valuationOf q 356 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 358 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (357)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning331 q) (meaning357 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 357 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 332 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (332)) (literal (valuationOf q) (358)) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 2 (meaning332 q) (meaning358 q) hs
  change valuationOf q 332 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 332 = false ∨ valuation q 358 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_right (literal (valuationOf q) (185)) (literal (valuationOf q) (359)) (countLit q [184]) (countLit q [185]) (count359 q) 1 (meaning185 q) (meaning359 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 359 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_left (literal (valuationOf q) (184)) (literal (valuationOf q) (359)) (countLit q [184]) (countLit q [185]) (count359 q) 1 (meaning184 q) (meaning359 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 359 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [183]) (countLit q [184, 185]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (361)) (countLit q [183]) (countLit q [184, 185]) (count361 q) 1 (meaning183 q) (meaning361 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 361 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 359 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_two (literal (valuationOf q) (183)) (literal (valuationOf q) (359)) (literal (valuationOf q) (362)) (countLit q [183]) (countLit q [184, 185]) (count361 q) 1 1 (meaning183 q) (meaning359 q) (meaning362 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 359 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 359 = false ∨ valuation q 362 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (367)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188]) (count367 q) 1 (meaning361 q) (meaning367 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 367 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (368)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188]) (count367 q) 2 (meaning362 q) (meaning368 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 368 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_right (literal (valuationOf q) (191)) (literal (valuationOf q) (369)) (countLit q [190]) (countLit q [191]) (count369 q) 1 (meaning191 q) (meaning369 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 369 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (375)) (countLit q [194]) (countLit q [195]) (count375 q) 1 (meaning194 q) (meaning375 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 375 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [192, 193]) (countLit q [194, 195]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (379)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count379 q) 1 (meaning371 q) (meaning379 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 379 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E175.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112175
