import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180, 181])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (353)) (countLit q [179]) (countLit q [180, 181]) (count353 q) 1 (meaning179 q) (meaning353 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 353 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_left (literal (valuationOf q) (182)) (literal (valuationOf q) (355)) (countLit q [182]) (countLit q [183]) (count355 q) 1 (meaning182 q) (meaning355 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 355 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_left (literal (valuationOf q) (184)) (literal (valuationOf q) (357)) (countLit q [184]) (countLit q [185]) (count357 q) 1 (meaning184 q) (meaning357 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 357 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [182, 183]) (countLit q [184, 185]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [182, 183]) (countLit q [184, 185]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (361)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count361 q) 1 (meaning353 q) (meaning361 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 361 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning188 q) (meaning363 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 363 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (375)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 (meaning361 q) (meaning375 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 375 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (377)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 (meaning349 q) (meaning377 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 377 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 1 (meaning349 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 195 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_two (literal (valuationOf q) (194)) (literal (valuationOf q) (195)) (literal (valuationOf q) (380)) (countLit q [194]) (countLit q [195]) (count379 q) 1 1 (meaning194 q) (meaning195 q) (meaning380 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 195 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 195 = false ∨ valuation q 380 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (380)) (literal (valuationOf q) (382)) (countLit q [193]) (countLit q [194, 195]) (count381 q) 2 (meaning380 q) (meaning382 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 382 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_right (literal (valuationOf q) (199)) (literal (valuationOf q) (385)) (countLit q [198]) (countLit q [199]) (count385 q) 1 (meaning199 q) (meaning385 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 385 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_two (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 1 (meaning383 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (388)) (literal (valuationOf q) (390)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 2 (meaning388 q) (meaning390 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 390 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (390)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 2 (meaning382 q) (meaning390 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 390 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 404 = true := by
  have hs : count403 q = (countLit q [193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206])
  have hm := merge_left (literal (valuationOf q) (390)) (literal (valuationOf q) (404)) (countLit q [193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206]) (count403 q) 2 (meaning390 q) (meaning404 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 404 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 421 = true := by
  have hs : count421 q = (countLit q [217]) + (countLit q [218]) := List.countP_append (p := literal q) (l₁ := [217]) (l₂ := [218])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (421)) (countLit q [217]) (countLit q [218]) (count421 q) 1 (meaning217 q) (meaning421 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 421 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 421 = false ∨ valuationOf q 425 = true := by
  have hs : count425 q = (countLit q [217, 218]) + (countLit q [219, 220]) := List.countP_append (p := literal q) (l₁ := [217, 218]) (l₂ := [219, 220])
  have hm := merge_left (literal (valuationOf q) (421)) (literal (valuationOf q) (425)) (countLit q [217, 218]) (countLit q [219, 220]) (count425 q) 1 (meaning421 q) (meaning425 q) hs
  change valuationOf q 421 = false ∨ valuationOf q 425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 421 = false ∨ valuation q 425 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 425 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [214, 215, 216]) + (countLit q [217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216]) (l₂ := [217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (425)) (literal (valuationOf q) (427)) (countLit q [214, 215, 216]) (countLit q [217, 218, 219, 220]) (count427 q) 1 (meaning425 q) (meaning427 q) hs
  change valuationOf q 425 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 425 = false ∨ valuation q 427 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 432 = true := by
  have hs : count431 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (432)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count431 q) 2 (meaning404 q) (meaning432 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 432 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 432 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_right (literal (valuationOf q) (432)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 2 (meaning432 q) (meaning434 q) hs
  change valuationOf q 432 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 432 = false ∨ valuation q 434 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (433)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 (meaning377 q) (meaning433 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 433 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true := by
  have hs : count433 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (431)) (literal (valuationOf q) (434)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]) (count433 q) 1 1 (meaning377 q) (meaning431 q) (meaning434 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 431 = false ∨ valuationOf q 434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 431 = false ∨ valuation q 434 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E123.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112123
