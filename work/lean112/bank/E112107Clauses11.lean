import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180, 181])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (353)) (countLit q [179]) (countLit q [180, 181]) (count353 q) 1 (meaning179 q) (meaning353 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 353 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (355)) (countLit q [182]) (countLit q [183]) (count355 q) 1 (meaning183 q) (meaning355 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 355 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_right (literal (valuationOf q) (185)) (literal (valuationOf q) (357)) (countLit q [184]) (countLit q [185]) (count357 q) 1 (meaning185 q) (meaning357 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 357 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_left (literal (valuationOf q) (184)) (literal (valuationOf q) (357)) (countLit q [184]) (countLit q [185]) (count357 q) 1 (meaning184 q) (meaning357 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 357 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [182, 183]) (countLit q [184, 185]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [182, 183]) (countLit q [184, 185]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_two (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (literal (valuationOf q) (360)) (countLit q [182, 183]) (countLit q [184, 185]) (count359 q) 1 1 (meaning355 q) (meaning357 q) (meaning360 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = false ∨ valuation q 360 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (360)) (literal (valuationOf q) (362)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count361 q) 2 (meaning360 q) (meaning362 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 362 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (361)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count361 q) 1 (meaning353 q) (meaning361 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 361 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 359 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_two (literal (valuationOf q) (353)) (literal (valuationOf q) (359)) (literal (valuationOf q) (362)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count361 q) 1 1 (meaning353 q) (meaning359 q) (meaning362 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 359 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 359 = false ∨ valuation q 362 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (365)) (countLit q [186]) (countLit q [187, 188]) (count365 q) 1 (meaning186 q) (meaning365 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 365 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (373)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (375)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 (meaning361 q) (meaning375 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 375 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192])
  have hm := merge_two (literal (valuationOf q) (361)) (literal (valuationOf q) (373)) (literal (valuationOf q) (376)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 1 (meaning361 q) (meaning373 q) (meaning376 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 373 = false ∨ valuation q 376 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (376)) (countLit q [179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192]) (count375 q) 2 (meaning362 q) (meaning376 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 376 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (376)) (literal (valuationOf q) (378)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 2 (meaning376 q) (meaning378 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 378 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (377)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 (meaning349 q) (meaning377 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 377 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_two (literal (valuationOf q) (349)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 1 (meaning349 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (378)) (countLit q [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 2 (meaning350 q) (meaning378 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 378 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_right (literal (valuationOf q) (195)) (literal (valuationOf q) (379)) (countLit q [194]) (countLit q [195]) (count379 q) 1 (meaning195 q) (meaning379 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 379 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (379)) (countLit q [194]) (countLit q [195]) (count379 q) 1 (meaning194 q) (meaning379 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 379 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [193]) (countLit q [194, 195]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [198]) + (countLit q [199]) := List.countP_append (p := literal q) (l₁ := [198]) (l₂ := [199])
  have hm := merge_left (literal (valuationOf q) (198)) (literal (valuationOf q) (385)) (countLit q [198]) (countLit q [199]) (count385 q) 1 (meaning198 q) (meaning385 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 385 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (387)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 (meaning383 q) (meaning387 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 387 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_two (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 1 (meaning383 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [193, 194, 195]) + (countLit q [196, 197, 198, 199]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195]) (l₂ := [196, 197, 198, 199])
  have hm := merge_right (literal (valuationOf q) (388)) (literal (valuationOf q) (390)) (countLit q [193, 194, 195]) (countLit q [196, 197, 198, 199]) (count389 q) 2 (meaning388 q) (meaning390 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 390 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E107.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112107
