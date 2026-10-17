import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178, 179])
  have hm := merge_two (literal (valuationOf q) (177)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [177]) (countLit q [178, 179]) (count353 q) 1 1 (meaning177 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_right (literal (valuationOf q) (182)) (literal (valuationOf q) (355)) (countLit q [181]) (countLit q [182]) (count355 q) 1 (meaning182 q) (meaning355 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 355 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [177, 178, 179]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [177, 178, 179]) (countLit q [181, 182, 183, 184]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [177, 178, 179]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (353)) (literal (valuationOf q) (361)) (countLit q [177, 178, 179]) (countLit q [181, 182, 183, 184]) (count361 q) 1 (meaning353 q) (meaning361 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 361 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [177, 178, 179]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (362)) (countLit q [177, 178, 179]) (countLit q [181, 182, 183, 184]) (count361 q) 2 (meaning354 q) (meaning362 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 362 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [186]) + (countLit q [187]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (363)) (countLit q [186]) (countLit q [187]) (count363 q) 1 (meaning186 q) (meaning363 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 363 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186, 187])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [185]) (countLit q [186, 187]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186, 187])
  have hm := merge_left (literal (valuationOf q) (185)) (literal (valuationOf q) (365)) (countLit q [185]) (countLit q [186, 187]) (count365 q) 1 (meaning185 q) (meaning365 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 365 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186, 187])
  have hm := merge_two (literal (valuationOf q) (185)) (literal (valuationOf q) (363)) (literal (valuationOf q) (366)) (countLit q [185]) (countLit q [186, 187]) (count365 q) 1 1 (meaning185 q) (meaning363 q) (meaning366 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 363 = false ∨ valuation q 366 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuationOf q) (188)) (literal (valuationOf q) (367)) (countLit q [188]) (countLit q [189]) (count367 q) 1 (meaning188 q) (meaning367 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 367 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [188, 189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [188, 189]) (l₂ := [190, 191])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (371)) (countLit q [188, 189]) (countLit q [190, 191]) (count371 q) 1 (meaning367 q) (meaning371 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 371 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [185, 186, 187]) + (countLit q [188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187]) (l₂ := [188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [185, 186, 187]) (countLit q [188, 189, 190, 191]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [185, 186, 187]) + (countLit q [188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187]) (l₂ := [188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (373)) (countLit q [185, 186, 187]) (countLit q [188, 189, 190, 191]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [185, 186, 187]) + (countLit q [188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187]) (l₂ := [188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (366)) (literal (valuationOf q) (374)) (countLit q [185, 186, 187]) (countLit q [188, 189, 190, 191]) (count373 q) 2 (meaning366 q) (meaning374 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 374 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [177, 178, 179, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (374)) (literal (valuationOf q) (376)) (countLit q [177, 178, 179, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 2 (meaning374 q) (meaning376 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 376 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (375)) (countLit q [177, 178, 179, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning361 q) (meaning375 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 375 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_two (literal (valuationOf q) (361)) (literal (valuationOf q) (373)) (literal (valuationOf q) (376)) (countLit q [177, 178, 179, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 1 (meaning361 q) (meaning373 q) (meaning376 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 373 = false ∨ valuation q 376 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (376)) (countLit q [177, 178, 179, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 2 (meaning362 q) (meaning376 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 376 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194]) (count377 q) 1 (meaning194 q) (meaning377 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 377 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_left (literal (valuationOf q) (193)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194]) (count377 q) 1 (meaning193 q) (meaning377 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 377 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193, 194])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [192]) (countLit q [193, 194]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193, 194])
  have hm := merge_left (literal (valuationOf q) (192)) (literal (valuationOf q) (379)) (countLit q [192]) (countLit q [193, 194]) (count379 q) 1 (meaning192 q) (meaning379 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 379 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193, 194])
  have hm := merge_two (literal (valuationOf q) (192)) (literal (valuationOf q) (377)) (literal (valuationOf q) (380)) (countLit q [192]) (countLit q [193, 194]) (count379 q) 1 1 (meaning192 q) (meaning377 q) (meaning380 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 377 = false ∨ valuation q 380 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_left (literal (valuationOf q) (195)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning195 q) (meaning381 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 381 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [195, 196]) (countLit q [197, 198]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (387)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 1 (meaning379 q) (meaning387 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 387 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 1 1 (meaning379 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (388)) (countLit q [192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 2 (meaning380 q) (meaning388 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 388 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_right (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E027.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112027
