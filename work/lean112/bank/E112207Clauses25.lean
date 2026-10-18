import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [186, 187]) + (countLit q [188, 189]) := List.countP_append (p := literal q) (l₁ := [186, 187]) (l₂ := [188, 189])
  have hm := merge_two (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (literal (valuationOf q) (370)) (countLit q [186, 187]) (countLit q [188, 189]) (count369 q) 1 1 (meaning365 q) (meaning367 q) (meaning370 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = false ∨ valuation q 370 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188, 189])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188, 189]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 370 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188, 189])
  have hm := merge_right (literal (valuationOf q) (370)) (literal (valuationOf q) (372)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188, 189]) (count371 q) 2 (meaning370 q) (meaning372 q) hs
  change valuationOf q 370 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 370 = false ∨ valuation q 372 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188, 189])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (371)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188, 189]) (count371 q) 1 (meaning363 q) (meaning371 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 371 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189])
  have hm := merge_right (literal (valuationOf q) (372)) (literal (valuationOf q) (374)) (countLit q [176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189]) (count373 q) 2 (meaning372 q) (meaning374 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 374 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (373)) (countLit q [176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189]) (count373 q) 1 (meaning359 q) (meaning373 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 373 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (371)) (literal (valuationOf q) (374)) (countLit q [176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189]) (count373 q) 1 1 (meaning359 q) (meaning371 q) (meaning374 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 371 = false ∨ valuation q 374 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (374)) (countLit q [176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189]) (count373 q) 2 (meaning360 q) (meaning374 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 374 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_right (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning191 q) (meaning375 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 375 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 192 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_two (literal (valuationOf q) (191)) (literal (valuationOf q) (192)) (literal (valuationOf q) (376)) (countLit q [191]) (countLit q [192]) (count375 q) 1 1 (meaning191 q) (meaning192 q) (meaning376 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 192 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 192 = false ∨ valuation q 376 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [190]) (countLit q [191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (376)) (literal (valuationOf q) (378)) (countLit q [190]) (countLit q [191, 192]) (count377 q) 2 (meaning376 q) (meaning378 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 378 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [193, 194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [193, 194]) (l₂ := [195, 196])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [193, 194]) (countLit q [195, 196]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (385)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 1 (meaning377 q) (meaning385 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 385 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195, 196]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195, 196])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (386)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195, 196]) (count385 q) 2 (meaning378 q) (meaning386 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 386 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (387)) (countLit q [197]) (countLit q [198]) (count387 q) 1 (meaning198 q) (meaning387 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 387 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 198 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_two (literal (valuationOf q) (197)) (literal (valuationOf q) (198)) (literal (valuationOf q) (388)) (countLit q [197]) (countLit q [198]) (count387 q) 1 1 (meaning197 q) (meaning198 q) (meaning388 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 198 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 198 = false ∨ valuation q 388 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [199]) + (countLit q [200]) := List.countP_append (p := literal q) (l₁ := [199]) (l₂ := [200])
  have hm := merge_left (literal (valuationOf q) (199)) (literal (valuationOf q) (389)) (countLit q [199]) (countLit q [200]) (count389 q) 1 (meaning199 q) (meaning389 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 389 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_right (literal (valuationOf q) (389)) (literal (valuationOf q) (391)) (countLit q [197, 198]) (countLit q [199, 200]) (count391 q) 1 (meaning389 q) (meaning391 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 391 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_left (literal (valuationOf q) (387)) (literal (valuationOf q) (391)) (countLit q [197, 198]) (countLit q [199, 200]) (count391 q) 1 (meaning387 q) (meaning391 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 391 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_two (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [197, 198]) (countLit q [199, 200]) (count391 q) 1 1 (meaning387 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_left (literal (valuationOf q) (388)) (literal (valuationOf q) (392)) (countLit q [197, 198]) (countLit q [199, 200]) (count391 q) 2 (meaning388 q) (meaning392 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 392 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [203]) + (countLit q [204]) := List.countP_append (p := literal q) (l₁ := [203]) (l₂ := [204])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (395)) (countLit q [203]) (countLit q [204]) (count395 q) 1 (meaning203 q) (meaning395 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 395 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 395 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [201, 202]) + (countLit q [203, 204]) := List.countP_append (p := literal q) (l₁ := [201, 202]) (l₂ := [203, 204])
  have hm := merge_right (literal (valuationOf q) (395)) (literal (valuationOf q) (397)) (countLit q [201, 202]) (countLit q [203, 204]) (count397 q) 1 (meaning395 q) (meaning397 q) hs
  change valuationOf q 395 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 395 = false ∨ valuation q 397 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [197, 198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [197, 198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [197, 198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (399)) (countLit q [197, 198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 1 (meaning391 q) (meaning399 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 399 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 400 = true := by
  have hs : count399 q = (countLit q [197, 198, 199, 200]) + (countLit q [201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [197, 198, 199, 200]) (l₂ := [201, 202, 203, 204])
  have hm := merge_left (literal (valuationOf q) (392)) (literal (valuationOf q) (400)) (countLit q [197, 198, 199, 200]) (countLit q [201, 202, 203, 204]) (count399 q) 2 (meaning392 q) (meaning400 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 400 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [190, 191, 192, 193, 194, 195, 196]) + (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192, 193, 194, 195, 196]) (l₂ := [197, 198, 199, 200, 201, 202, 203, 204])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [190, 191, 192, 193, 194, 195, 196]) (countLit q [197, 198, 199, 200, 201, 202, 203, 204]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E207.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112207
