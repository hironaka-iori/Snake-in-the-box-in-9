import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_right (literal (valuationOf q) (166)) (literal (valuationOf q) (325)) (countLit q [165]) (countLit q [166]) (count325 q) 1 (meaning166 q) (meaning325 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 325 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [164]) (countLit q [165, 166]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (329)) (countLit q [168]) (countLit q [169]) (count329 q) 1 (meaning168 q) (meaning329 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 329 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [167]) (countLit q [168, 169]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (333)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169]) (count333 q) 1 (meaning327 q) (meaning333 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 333 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_right (literal (valuationOf q) (172)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172]) (count335 q) 1 (meaning172 q) (meaning335 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 335 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171, 172])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [170]) (countLit q [171, 172]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171, 172])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (337)) (countLit q [170]) (countLit q [171, 172]) (count337 q) 1 (meaning170 q) (meaning337 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 337 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 335 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171, 172])
  have hm := merge_two (literal (valuationOf q) (170)) (literal (valuationOf q) (335)) (literal (valuationOf q) (338)) (countLit q [170]) (countLit q [171, 172]) (count337 q) 1 1 (meaning170 q) (meaning335 q) (meaning338 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 335 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 335 = false ∨ valuation q 338 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (339)) (countLit q [173]) (countLit q [174]) (count339 q) 1 (meaning173 q) (meaning339 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 339 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (341)) (countLit q [175]) (countLit q [176]) (count341 q) 1 (meaning175 q) (meaning341 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 341 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [173, 174]) (countLit q [175, 176]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (343)) (countLit q [173, 174]) (countLit q [175, 176]) (count343 q) 1 (meaning339 q) (meaning343 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 343 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175, 176]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (345)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175, 176]) (count345 q) 1 (meaning337 q) (meaning345 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 345 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (337)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175, 176]) (count345 q) 1 1 (meaning337 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (338)) (literal (valuationOf q) (346)) (countLit q [170, 171, 172]) (countLit q [173, 174, 175, 176]) (count345 q) 2 (meaning338 q) (meaning346 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 346 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (347)) (countLit q [164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning333 q) (meaning347 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 347 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (333)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 1 (meaning333 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (349)) (countLit q [178]) (countLit q [179]) (count349 q) 1 (meaning178 q) (meaning349 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 349 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178, 179])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [177]) (countLit q [178, 179]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_right (literal (valuationOf q) (181)) (literal (valuationOf q) (353)) (countLit q [180]) (countLit q [181]) (count353 q) 1 (meaning181 q) (meaning353 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 353 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_left (literal (valuationOf q) (180)) (literal (valuationOf q) (353)) (countLit q [180]) (countLit q [181]) (count353 q) 1 (meaning180 q) (meaning353 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 353 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 181 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_two (literal (valuationOf q) (180)) (literal (valuationOf q) (181)) (literal (valuationOf q) (354)) (countLit q [180]) (countLit q [181]) (count353 q) 1 1 (meaning180 q) (meaning181 q) (meaning354 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 181 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 181 = false ∨ valuation q 354 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (355)) (countLit q [182]) (countLit q [183]) (count355 q) 1 (meaning183 q) (meaning355 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 355 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [180, 181]) (countLit q [182, 183]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (357)) (countLit q [180, 181]) (countLit q [182, 183]) (count357 q) 1 (meaning353 q) (meaning357 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 357 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (358)) (countLit q [180, 181]) (countLit q [182, 183]) (count357 q) 2 (meaning354 q) (meaning358 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 358 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [177, 178, 179]) (countLit q [180, 181, 182, 183]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E201.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112201
