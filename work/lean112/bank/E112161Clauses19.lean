import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [177, 178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [177, 178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (349)) (countLit q [177, 178]) (countLit q [179, 180]) (count349 q) 1 (meaning345 q) (meaning349 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 349 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [177, 178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [177, 178]) (l₂ := [179, 180])
  have hm := merge_two (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [177, 178]) (countLit q [179, 180]) (count349 q) 1 1 (meaning345 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179, 180]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (350)) (literal (valuationOf q) (352)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179, 180]) (count351 q) 2 (meaning350 q) (meaning352 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 352 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (351)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179, 180]) (count351 q) 1 (meaning343 q) (meaning351 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 351 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (349)) (literal (valuationOf q) (352)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179, 180]) (count351 q) 1 1 (meaning343 q) (meaning349 q) (meaning352 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 349 = false ∨ valuation q 352 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 352 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (352)) (literal (valuationOf q) (354)) (countLit q [168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180]) (count353 q) 2 (meaning352 q) (meaning354 q) hs
  change valuationOf q 352 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 352 = false ∨ valuation q 354 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (353)) (countLit q [168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180]) (count353 q) 1 (meaning339 q) (meaning353 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 353 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [168, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [168, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180]) (count353 q) 1 1 (meaning339 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (355)) (countLit q [182]) (countLit q [183]) (count355 q) 1 (meaning183 q) (meaning355 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 355 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [181]) (countLit q [182, 183]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (357)) (countLit q [181]) (countLit q [182, 183]) (count357 q) 1 (meaning181 q) (meaning357 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 357 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 355 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_two (literal (valuationOf q) (181)) (literal (valuationOf q) (355)) (literal (valuationOf q) (358)) (countLit q [181]) (countLit q [182, 183]) (count357 q) 1 1 (meaning181 q) (meaning355 q) (meaning358 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 355 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 355 = false ∨ valuation q 358 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_right (literal (valuationOf q) (185)) (literal (valuationOf q) (359)) (countLit q [184]) (countLit q [185]) (count359 q) 1 (meaning185 q) (meaning359 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 359 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [186]) + (countLit q [187]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187])
  have hm := merge_right (literal (valuationOf q) (187)) (literal (valuationOf q) (361)) (countLit q [186]) (countLit q [187]) (count361 q) 1 (meaning187 q) (meaning361 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 361 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [184, 185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [184, 185]) (l₂ := [186, 187])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [184, 185]) (countLit q [186, 187]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [184, 185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [184, 185]) (l₂ := [186, 187])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (363)) (countLit q [184, 185]) (countLit q [186, 187]) (count363 q) 1 (meaning359 q) (meaning363 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 363 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [181, 182, 183]) + (countLit q [184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183]) (l₂ := [184, 185, 186, 187])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [181, 182, 183]) (countLit q [184, 185, 186, 187]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [181, 182, 183]) + (countLit q [184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183]) (l₂ := [184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (365)) (countLit q [181, 182, 183]) (countLit q [184, 185, 186, 187]) (count365 q) 1 (meaning357 q) (meaning365 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 365 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 358 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [181, 182, 183]) + (countLit q [184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183]) (l₂ := [184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (358)) (literal (valuationOf q) (366)) (countLit q [181, 182, 183]) (countLit q [184, 185, 186, 187]) (count365 q) 2 (meaning358 q) (meaning366 q) hs
  change valuationOf q 358 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 366 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (367)) (countLit q [189]) (countLit q [190]) (count367 q) 1 (meaning189 q) (meaning367 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 367 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [188]) (countLit q [189, 190]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_right (literal (valuationOf q) (192)) (literal (valuationOf q) (371)) (countLit q [191]) (countLit q [192]) (count371 q) 1 (meaning192 q) (meaning371 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 371 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (371)) (countLit q [191]) (countLit q [192]) (count371 q) 1 (meaning191 q) (meaning371 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 371 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191, 192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [191, 192]) (l₂ := [193, 194])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (375)) (countLit q [191, 192]) (countLit q [193, 194]) (count375 q) 1 (meaning371 q) (meaning375 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 375 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [188, 189, 190]) (countLit q [191, 192, 193, 194]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (377)) (countLit q [188, 189, 190]) (countLit q [191, 192, 193, 194]) (count377 q) 1 (meaning369 q) (meaning377 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 377 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (379)) (countLit q [181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194]) (count379 q) 1 (meaning365 q) (meaning379 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 379 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [181, 182, 183, 184, 185, 186, 187]) + (countLit q [188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183, 184, 185, 186, 187]) (l₂ := [188, 189, 190, 191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (366)) (literal (valuationOf q) (380)) (countLit q [181, 182, 183, 184, 185, 186, 187]) (countLit q [188, 189, 190, 191, 192, 193, 194]) (count379 q) 2 (meaning366 q) (meaning380 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 380 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E161.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112161
