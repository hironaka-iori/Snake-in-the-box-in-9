import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_two (literal (valuationOf q) (303)) (literal (valuationOf q) (363)) (literal (valuationOf q) (366)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count365 q) 1 1 (meaning303 q) (meaning363 q) (meaning366 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 363 = false ∨ valuation q 366 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (304)) (literal (valuationOf q) (366)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (count365 q) 2 (meaning304 q) (meaning366 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 366 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (369)) (countLit q [186]) (countLit q [187, 188]) (count369 q) 1 (meaning186 q) (meaning369 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 369 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 190 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_two (literal (valuationOf q) (189)) (literal (valuationOf q) (190)) (literal (valuationOf q) (372)) (countLit q [189]) (countLit q [190]) (count371 q) 1 1 (meaning189 q) (meaning190 q) (meaning372 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 190 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 190 = false ∨ valuation q 372 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [189, 190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [189, 190]) (l₂ := [191, 192])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (375)) (countLit q [189, 190]) (countLit q [191, 192]) (count375 q) 1 (meaning371 q) (meaning375 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 375 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [189, 190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [189, 190]) (l₂ := [191, 192])
  have hm := merge_left (literal (valuationOf q) (372)) (literal (valuationOf q) (376)) (countLit q [189, 190]) (countLit q [191, 192]) (count375 q) 2 (meaning372 q) (meaning376 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 376 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (376)) (literal (valuationOf q) (378)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count377 q) 2 (meaning376 q) (meaning378 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 378 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (377)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191, 192]) (count377 q) 1 (meaning369 q) (meaning377 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 377 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [193, 194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [193, 194]) (l₂ := [195, 196])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [193, 194]) (countLit q [195, 196]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (385)) (countLit q [197]) (countLit q [198]) (count385 q) 1 (meaning198 q) (meaning385 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 385 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_left (literal (valuationOf q) (385)) (literal (valuationOf q) (389)) (countLit q [197, 198]) (countLit q [199, 200]) (count389 q) 1 (meaning385 q) (meaning389 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 389 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [193, 194, 195, 196]) + (countLit q [197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196]) (l₂ := [197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [193, 194, 195, 196]) (countLit q [197, 198, 199, 200]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [193, 194, 195, 196]) + (countLit q [197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196]) (l₂ := [197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (391)) (countLit q [193, 194, 195, 196]) (countLit q [197, 198, 199, 200]) (count391 q) 1 (meaning383 q) (meaning391 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 391 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (391)) (literal (valuationOf q) (393)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 1 (meaning391 q) (meaning393 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 393 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (393)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 1 (meaning377 q) (meaning393 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 393 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (391)) (literal (valuationOf q) (394)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 1 1 (meaning377 q) (meaning391 q) (meaning394 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 391 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 391 = false ∨ valuation q 394 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 394 = true := by
  have hs : count393 q = (countLit q [186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (394)) (countLit q [186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200]) (count393 q) 2 (meaning378 q) (meaning394 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 394 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (395)) (countLit q [202]) (countLit q [203]) (count395 q) 1 (meaning203 q) (meaning395 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 395 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201]) + (countLit q [202, 203]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202, 203])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [201]) (countLit q [202, 203]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201]) + (countLit q [202, 203]) := List.countP_append (p := literal q) (l₁ := [201]) (l₂ := [202, 203])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (397)) (countLit q [201]) (countLit q [202, 203]) (count397 q) 1 (meaning201 q) (meaning397 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 397 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_right (literal (valuationOf q) (207)) (literal (valuationOf q) (401)) (countLit q [206]) (countLit q [207]) (count401 q) 1 (meaning207 q) (meaning401 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 401 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 206 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [206]) + (countLit q [207]) := List.countP_append (p := literal q) (l₁ := [206]) (l₂ := [207])
  have hm := merge_left (literal (valuationOf q) (206)) (literal (valuationOf q) (401)) (countLit q [206]) (countLit q [207]) (count401 q) 1 (meaning206 q) (meaning401 q) hs
  change valuationOf q 206 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 206 = false ∨ valuation q 401 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [204, 205]) + (countLit q [206, 207]) := List.countP_append (p := literal q) (l₁ := [204, 205]) (l₂ := [206, 207])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [204, 205]) (countLit q [206, 207]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [201, 202, 203]) + (countLit q [204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [201, 202, 203]) (l₂ := [204, 205, 206, 207])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [201, 202, 203]) (countLit q [204, 205, 206, 207]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [201, 202, 203]) + (countLit q [204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [201, 202, 203]) (l₂ := [204, 205, 206, 207])
  have hm := merge_left (literal (valuationOf q) (397)) (literal (valuationOf q) (405)) (countLit q [201, 202, 203]) (countLit q [204, 205, 206, 207]) (count405 q) 1 (meaning397 q) (meaning405 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 405 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true := by
  have hs : count405 q = (countLit q [201, 202, 203]) + (countLit q [204, 205, 206, 207]) := List.countP_append (p := literal q) (l₁ := [201, 202, 203]) (l₂ := [204, 205, 206, 207])
  have hm := merge_two (literal (valuationOf q) (397)) (literal (valuationOf q) (403)) (literal (valuationOf q) (406)) (countLit q [201, 202, 203]) (countLit q [204, 205, 206, 207]) (count405 q) 1 1 (meaning397 q) (meaning403 q) (meaning406 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 403 = false ∨ valuationOf q 406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 403 = false ∨ valuation q 406 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning213 q) (meaning413 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 413 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [212, 213]) + (countLit q [214, 215]) := List.countP_append (p := literal q) (l₁ := [212, 213]) (l₂ := [214, 215])
  have hm := merge_left (literal (valuationOf q) (413)) (literal (valuationOf q) (417)) (countLit q [212, 213]) (countLit q [214, 215]) (count417 q) 1 (meaning413 q) (meaning417 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 417 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [208, 209, 210, 211]) + (countLit q [212, 213, 214, 215]) := List.countP_append (p := literal q) (l₁ := [208, 209, 210, 211]) (l₂ := [212, 213, 214, 215])
  have hm := merge_right (literal (valuationOf q) (417)) (literal (valuationOf q) (419)) (countLit q [208, 209, 210, 211]) (countLit q [212, 213, 214, 215]) (count419 q) 1 (meaning417 q) (meaning419 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 419 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E097.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112097
