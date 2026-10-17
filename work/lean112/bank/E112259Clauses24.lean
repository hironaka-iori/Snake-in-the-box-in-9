import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_right (literal (valuationOf q) (186)) (literal (valuationOf q) (361)) (countLit q [185]) (countLit q [186]) (count361 q) 1 (meaning186 q) (meaning361 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 361 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning188 q) (meaning363 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 363 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning187 q) (meaning363 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 363 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (365)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 (meaning361 q) (meaning365 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 365 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_two (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (literal (valuationOf q) (366)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 1 (meaning361 q) (meaning363 q) (meaning366 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = false ∨ valuation q 366 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (366)) (literal (valuationOf q) (368)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 2 (meaning366 q) (meaning368 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 368 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (367)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning359 q) (meaning367 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 367 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (368)) (literal (valuationOf q) (370)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 2 (meaning368 q) (meaning370 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 370 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning355 q) (meaning369 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 369 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_two (literal (valuationOf q) (355)) (literal (valuationOf q) (367)) (literal (valuationOf q) (370)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 1 (meaning355 q) (meaning367 q) (meaning370 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 367 = false ∨ valuation q 370 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuationOf q) (193)) (literal (valuationOf q) (375)) (countLit q [192]) (countLit q [193]) (count375 q) 1 (meaning193 q) (meaning375 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 375 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_left (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [192]) (countLit q [193]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_right (literal (valuationOf q) (195)) (literal (valuationOf q) (377)) (countLit q [194]) (countLit q [195]) (count377 q) 1 (meaning195 q) (meaning377 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 377 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [192, 193]) (countLit q [194, 195]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192, 193]) + (countLit q [194, 195]) := List.countP_append (p := literal q) (l₁ := [192, 193]) (l₂ := [194, 195])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (379)) (countLit q [192, 193]) (countLit q [194, 195]) (count379 q) 1 (meaning375 q) (meaning379 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 379 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [189, 190, 191]) + (countLit q [192, 193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191]) (l₂ := [192, 193, 194, 195])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [189, 190, 191]) (countLit q [192, 193, 194, 195]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuationOf q) (197)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning197 q) (meaning383 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 383 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (383)) (countLit q [196]) (countLit q [197]) (count383 q) 1 (meaning196 q) (meaning383 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 383 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [196, 197]) + (countLit q [198, 199]) := List.countP_append (p := literal q) (l₁ := [196, 197]) (l₂ := [198, 199])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (387)) (countLit q [196, 197]) (countLit q [198, 199]) (count387 q) 1 (meaning383 q) (meaning387 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 387 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (391)) (countLit q [202]) (countLit q [203]) (count391 q) 1 (meaning202 q) (meaning391 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 391 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200, 201]) + (countLit q [202, 203]) := List.countP_append (p := literal q) (l₁ := [200, 201]) (l₂ := [202, 203])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [200, 201]) (countLit q [202, 203]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198, 199]) + (countLit q [200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199]) (l₂ := [200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198, 199]) (countLit q [200, 201, 202, 203]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198, 199]) + (countLit q [200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199]) (l₂ := [200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198, 199]) (countLit q [200, 201, 202, 203]) (count395 q) 1 (meaning387 q) (meaning395 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 395 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (397)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 (meaning381 q) (meaning397 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 397 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 395 = false ∨ valuationOf q 398 = true := by
  have hs : count397 q = (countLit q [189, 190, 191, 192, 193, 194, 195]) + (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [189, 190, 191, 192, 193, 194, 195]) (l₂ := [196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (395)) (literal (valuationOf q) (398)) (countLit q [189, 190, 191, 192, 193, 194, 195]) (countLit q [196, 197, 198, 199, 200, 201, 202, 203]) (count397 q) 1 1 (meaning381 q) (meaning395 q) (meaning398 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 395 = false ∨ valuationOf q 398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 395 = false ∨ valuation q 398 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 398 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (398)) (literal (valuationOf q) (400)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 2 (meaning398 q) (meaning400 q) hs
  change valuationOf q 398 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 398 = false ∨ valuation q 400 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) + (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (l₂ := [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (399)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]) (countLit q [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]) (count399 q) 1 (meaning369 q) (meaning399 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 399 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E259.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112259
