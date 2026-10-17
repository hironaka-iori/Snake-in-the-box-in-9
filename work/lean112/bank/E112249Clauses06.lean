import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (361)) (countLit q [173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185]) (count361 q) 1 (meaning347 q) (meaning361 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 361 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (348)) (literal (valuationOf q) (362)) (countLit q [173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185]) (count361 q) 2 (meaning348 q) (meaning362 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 362 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 364 = true := by
  have hs : count363 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (362)) (literal (valuationOf q) (364)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 2 (meaning362 q) (meaning364 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 364 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (363)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 1 (meaning337 q) (meaning363 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 363 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 361 = false ∨ valuationOf q 364 = true := by
  have hs : count363 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_two (literal (valuationOf q) (337)) (literal (valuationOf q) (361)) (literal (valuationOf q) (364)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 1 1 (meaning337 q) (meaning361 q) (meaning364 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 361 = false ∨ valuationOf q 364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 361 = false ∨ valuation q 364 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 364 = true := by
  have hs : count363 q = (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) + (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (l₂ := [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (338)) (literal (valuationOf q) (364)) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]) (countLit q [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count363 q) 2 (meaning338 q) (meaning364 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 364 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning187 q) (meaning365 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 365 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [186]) (countLit q [187, 188]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (367)) (countLit q [186]) (countLit q [187, 188]) (count367 q) 1 (meaning186 q) (meaning367 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 367 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (369)) (countLit q [190]) (countLit q [191]) (count369 q) 1 (meaning190 q) (meaning369 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 369 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190, 191]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count373 q) 1 (meaning367 q) (meaning373 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 373 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193, 194])
  have hm := merge_left (literal (valuationOf q) (192)) (literal (valuationOf q) (377)) (countLit q [192]) (countLit q [193, 194]) (count377 q) 1 (meaning192 q) (meaning377 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 377 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (381)) (countLit q [197]) (countLit q [198]) (count381 q) 1 (meaning198 q) (meaning381 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 381 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [195, 196]) (countLit q [197, 198]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (385)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count385 q) 1 (meaning377 q) (meaning385 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 385 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (383)) (literal (valuationOf q) (386)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count385 q) 1 1 (meaning377 q) (meaning383 q) (meaning386 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 383 = false ∨ valuation q 386 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 386 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (386)) (literal (valuationOf q) (388)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 2 (meaning386 q) (meaning388 q) hs
  change valuationOf q 386 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 386 = false ∨ valuation q 388 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (387)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning373 q) (meaning387 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 387 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 1 (meaning373 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_right (literal (valuationOf q) (201)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning201 q) (meaning389 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 389 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [199, 200, 201]) + (countLit q [202, 203, 204, 205]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201]) (l₂ := [202, 203, 204, 205])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (399)) (countLit q [199, 200, 201]) (countLit q [202, 203, 204, 205]) (count399 q) 1 (meaning391 q) (meaning399 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 399 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 210 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_right (literal (valuationOf q) (210)) (literal (valuationOf q) (405)) (countLit q [209]) (countLit q [210]) (count405 q) 1 (meaning210 q) (meaning405 q) hs
  change valuationOf q 210 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 405 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 210 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [209]) + (countLit q [210]) := List.countP_append (p := literal q) (l₁ := [209]) (l₂ := [210])
  have hm := merge_two (literal (valuationOf q) (209)) (literal (valuationOf q) (210)) (literal (valuationOf q) (406)) (countLit q [209]) (countLit q [210]) (count405 q) 1 1 (meaning209 q) (meaning210 q) (meaning406 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 210 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 210 = false ∨ valuation q 406 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (409)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 1 (meaning405 q) (meaning409 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 409 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [209, 210]) + (countLit q [211, 212]) := List.countP_append (p := literal q) (l₁ := [209, 210]) (l₂ := [211, 212])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (410)) (countLit q [209, 210]) (countLit q [211, 212]) (count409 q) 2 (meaning406 q) (meaning410 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 410 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E249.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112249
