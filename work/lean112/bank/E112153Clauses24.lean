import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 365 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_two (literal (valuationOf q) (305)) (literal (valuationOf q) (365)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 1 (meaning305 q) (meaning365 q) (meaning368 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 365 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 365 = false ∨ valuation q 368 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (306)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 2 (meaning306 q) (meaning368 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 368 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuationOf q) (188)) (literal (valuationOf q) (369)) (countLit q [188]) (countLit q [189]) (count369 q) 1 (meaning188 q) (meaning369 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 369 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188, 189])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [187]) (countLit q [188, 189]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_right (literal (valuationOf q) (191)) (literal (valuationOf q) (373)) (countLit q [190]) (countLit q [191]) (count373 q) 1 (meaning191 q) (meaning373 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 373 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (373)) (countLit q [190]) (countLit q [191]) (count373 q) 1 (meaning190 q) (meaning373 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 373 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 191 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_two (literal (valuationOf q) (190)) (literal (valuationOf q) (191)) (literal (valuationOf q) (374)) (countLit q [190]) (countLit q [191]) (count373 q) 1 1 (meaning190 q) (meaning191 q) (meaning374 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 191 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 191 = false ∨ valuation q 374 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuationOf q) (193)) (literal (valuationOf q) (375)) (countLit q [192]) (countLit q [193]) (count375 q) 1 (meaning193 q) (meaning375 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 375 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (377)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 1 (meaning373 q) (meaning377 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 377 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [190, 191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [190, 191]) (l₂ := [192, 193])
  have hm := merge_left (literal (valuationOf q) (374)) (literal (valuationOf q) (378)) (countLit q [190, 191]) (countLit q [192, 193]) (count377 q) 2 (meaning374 q) (meaning378 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 378 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_right (literal (valuationOf q) (378)) (literal (valuationOf q) (380)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 2 (meaning378 q) (meaning380 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 380 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (379)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 1 (meaning371 q) (meaning379 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 379 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [187, 188, 189]) + (countLit q [190, 191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189]) (l₂ := [190, 191, 192, 193])
  have hm := merge_two (literal (valuationOf q) (371)) (literal (valuationOf q) (377)) (literal (valuationOf q) (380)) (countLit q [187, 188, 189]) (countLit q [190, 191, 192, 193]) (count379 q) 1 1 (meaning371 q) (meaning377 q) (meaning380 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 377 = false ∨ valuation q 380 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (381)) (countLit q [194]) (countLit q [195]) (count381 q) 1 (meaning194 q) (meaning381 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 381 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [194, 195]) (countLit q [196, 197]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_right (literal (valuationOf q) (201)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning201 q) (meaning389 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 389 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [198, 199]) (countLit q [200, 201]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (393)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 (meaning385 q) (meaning393 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 393 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [194, 195, 196, 197]) + (countLit q [198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196, 197]) (l₂ := [198, 199, 200, 201])
  have hm := merge_two (literal (valuationOf q) (385)) (literal (valuationOf q) (391)) (literal (valuationOf q) (394)) (countLit q [194, 195, 196, 197]) (countLit q [198, 199, 200, 201]) (count393 q) 1 1 (meaning385 q) (meaning391 q) (meaning394 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 391 = false ∨ valuation q 394 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 394 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_right (literal (valuationOf q) (394)) (literal (valuationOf q) (396)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 2 (meaning394 q) (meaning396 q) hs
  change valuationOf q 394 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 394 = false ∨ valuation q 396 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (395)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 (meaning379 q) (meaning395 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 395 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (393)) (literal (valuationOf q) (396)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 1 1 (meaning379 q) (meaning393 q) (meaning396 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 393 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 393 = false ∨ valuation q 396 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 396 = true := by
  have hs : count395 q = (countLit q [187, 188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200, 201])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (396)) (countLit q [187, 188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200, 201]) (count395 q) 2 (meaning380 q) (meaning396 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 396 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203]) (count397 q) 1 (meaning203 q) (meaning397 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 397 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 202 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_left (literal (valuationOf q) (202)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203]) (count397 q) 1 (meaning202 q) (meaning397 q) hs
  change valuationOf q 202 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 202 = false ∨ valuation q 397 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning397 q) (meaning401 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 401 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_right (literal (valuationOf q) (207)) (literal (valuationOf q) (403)) (countLit q [206]) (countLit q [207]) (count403 q) 1 (meaning207 q) (meaning403 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 403 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E153.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112153
