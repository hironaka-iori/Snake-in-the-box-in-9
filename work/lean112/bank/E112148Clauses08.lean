import E112148Semantics
import B112E148Inputs
namespace Snake9.Regrowth.E112148
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [167]) (countLit q [168, 169]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168, 169])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (333)) (countLit q [167]) (countLit q [168, 169]) (count333 q) 1 (meaning167 q) (meaning333 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 333 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_left (literal (valuationOf q) (171)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172]) (count335 q) 1 (meaning171 q) (meaning335 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 335 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171, 172])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [170]) (countLit q [171, 172]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [167, 168, 169]) + (countLit q [170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169]) (l₂ := [170, 171, 172])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (339)) (countLit q [167, 168, 169]) (countLit q [170, 171, 172]) (count339 q) 1 (meaning333 q) (meaning339 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 339 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [167, 168, 169, 170, 171, 172]) + (countLit q [174, 175, 176, 177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172]) (l₂ := [174, 175, 176, 177, 178, 179, 180])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (353)) (countLit q [167, 168, 169, 170, 171, 172]) (countLit q [174, 175, 176, 177, 178, 179, 180]) (count353 q) 1 (meaning339 q) (meaning353 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 353 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (357)) (countLit q [181]) (countLit q [182, 183]) (count357 q) 1 (meaning181 q) (meaning357 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 357 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [181, 182, 183]) + (countLit q [184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183]) (l₂ := [184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (365)) (countLit q [181, 182, 183]) (countLit q [184, 185, 186, 187]) (count365 q) 1 (meaning357 q) (meaning365 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 365 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (373)) (countLit q [193]) (countLit q [194]) (count373 q) 1 (meaning194 q) (meaning373 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 373 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191, 192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [191, 192]) (l₂ := [193, 194])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [191, 192]) (countLit q [193, 194]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [188, 189, 190]) (countLit q [191, 192, 193, 194]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (379)) (countLit q [181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194]) (count379 q) 1 (meaning365 q) (meaning379 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 379 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (381)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 1 (meaning353 q) (meaning381 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 381 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 379 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_two (literal (valuationOf q) (353)) (literal (valuationOf q) (379)) (literal (valuationOf q) (382)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 1 1 (meaning353 q) (meaning379 q) (meaning382 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 379 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 379 = false ∨ valuation q 382 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_left (literal (valuationOf q) (198)) (literal (valuationOf q) (387)) (countLit q [198]) (countLit q [199]) (count387 q) 1 (meaning198 q) (meaning387 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 387 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 1 (meaning387 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (392)) (literal (valuationOf q) (394)) (countLit q [195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 2 (meaning392 q) (meaning394 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 394 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (393)) (literal (valuationOf q) (407)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count407 q) 1 (meaning393 q) (meaning407 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 407 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 408 = true := by
  have hs : count407 q = (countLit q [195, 196, 197, 198, 199, 200, 201]) + (countLit q [202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201]) (l₂ := [202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (394)) (literal (valuationOf q) (408)) (countLit q [195, 196, 197, 198, 199, 200, 201]) (countLit q [202, 203, 204, 205, 206, 207, 208]) (count407 q) 2 (meaning394 q) (meaning408 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 408 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 435 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (407)) (literal (valuationOf q) (435)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 1 (meaning407 q) (meaning435 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 435 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) + (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (l₂ := [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (408)) (literal (valuationOf q) (436)) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (countLit q [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count435 q) 2 (meaning408 q) (meaning436 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 436 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_right (literal (valuationOf q) (436)) (literal (valuationOf q) (438)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning436 q) (meaning438 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 438 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (437)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 (meaning381 q) (meaning437 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 437 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (435)) (literal (valuationOf q) (438)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 1 1 (meaning381 q) (meaning435 q) (meaning438 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 435 = false ∨ valuation q 438 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) + (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (l₂ := [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (438)) (countLit q [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (countLit q [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count437 q) 2 (meaning382 q) (meaning438 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 438 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E148.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112148
