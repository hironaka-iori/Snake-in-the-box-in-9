import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 682 = false ∨ valuationOf q 696 = false ∨ valuationOf q 706 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (682)) (literal (valuationOf q) (696)) (literal (valuationOf q) (706)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 4 2 (meaning682 q) (meaning696 q) (meaning706 q) hs
  change valuationOf q 682 = false ∨ valuationOf q 696 = false ∨ valuationOf q 706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 682 = false ∨ valuation q 696 = false ∨ valuation q 706 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 683 = false ∨ valuationOf q 695 = false ∨ valuationOf q 706 = true := by
  have hs : count701 q = (countLit q [-1, -3, -6, -7, -9, -11]) + (countLit q [-13, -14, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11]) (l₂ := [-13, -14, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (683)) (literal (valuationOf q) (695)) (literal (valuationOf q) (706)) (countLit q [-1, -3, -6, -7, -9, -11]) (countLit q [-13, -14, -18, -21, -22, -25]) (count701 q) 5 1 (meaning683 q) (meaning695 q) (meaning706 q) hs
  change valuationOf q 683 = false ∨ valuationOf q 695 = false ∨ valuationOf q 706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 683 = false ∨ valuation q 695 = false ∨ valuation q 706 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 710 = true := by
  have hs : count710 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (710)) (countLit q [-28]) (countLit q [-30]) (count710 q) 1 (meaningNeg30 q) (meaning710 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 710 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 710 = true := by
  have hs : count710 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (710)) (countLit q [-28]) (countLit q [-30]) (count710 q) 1 (meaningNeg28 q) (meaning710 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 710 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 710 = false ∨ valuationOf q 712 = true := by
  have hs : count712 q = (countLit q [-26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (710)) (literal (valuationOf q) (712)) (countLit q [-26]) (countLit q [-28, -30]) (count712 q) 1 (meaning710 q) (meaning712 q) hs
  change valuationOf q 710 = false ∨ valuationOf q 712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 710 = false ∨ valuation q 712 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 712 = true := by
  have hs : count712 q = (countLit q [-26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (712)) (countLit q [-26]) (countLit q [-28, -30]) (count712 q) 1 (meaningNeg26 q) (meaning712 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 712 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 712 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 710 = false ∨ valuationOf q 713 = true := by
  have hs : count712 q = (countLit q [-26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (710)) (literal (valuationOf q) (713)) (countLit q [-26]) (countLit q [-28, -30]) (count712 q) 1 1 (meaningNeg26 q) (meaning710 q) (meaning713 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 710 = false ∨ valuationOf q 713 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 710 = false ∨ valuation q 713 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 715 = true := by
  have hs : count715 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (715)) (countLit q [-33]) (countLit q [-35]) (count715 q) 1 (meaningNeg35 q) (meaning715 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 715 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 715 = true := by
  have hs : count715 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (715)) (countLit q [-33]) (countLit q [-35]) (count715 q) 1 (meaningNeg33 q) (meaning715 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 715 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 35 = true ∨ valuationOf q 716 = true := by
  have hs : count715 q = (countLit q [-33]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (716)) (countLit q [-33]) (countLit q [-35]) (count715 q) 1 1 (meaningNeg33 q) (meaningNeg35 q) (meaning716 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 35 = true ∨ valuation q 716 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 715 = false ∨ valuationOf q 717 = true := by
  have hs : count717 q = (countLit q [-31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (715)) (literal (valuationOf q) (717)) (countLit q [-31]) (countLit q [-33, -35]) (count717 q) 1 (meaning715 q) (meaning717 q) hs
  change valuationOf q 715 = false ∨ valuationOf q 717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 715 = false ∨ valuation q 717 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 716 = false ∨ valuationOf q 718 = true := by
  have hs : count717 q = (countLit q [-31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -35])
  have hm := merge_right (literal (valuationOf q) (716)) (literal (valuationOf q) (718)) (countLit q [-31]) (countLit q [-33, -35]) (count717 q) 2 (meaning716 q) (meaning718 q) hs
  change valuationOf q 716 = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 716 = false ∨ valuation q 718 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 717 = true := by
  have hs : count717 q = (countLit q [-31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (717)) (countLit q [-31]) (countLit q [-33, -35]) (count717 q) 1 (meaningNeg31 q) (meaning717 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 717 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 715 = false ∨ valuationOf q 718 = true := by
  have hs : count717 q = (countLit q [-31]) + (countLit q [-33, -35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-33, -35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (715)) (literal (valuationOf q) (718)) (countLit q [-31]) (countLit q [-33, -35]) (count717 q) 1 1 (meaningNeg31 q) (meaning715 q) (meaning718 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 715 = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 715 = false ∨ valuation q 718 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 717 = false ∨ valuationOf q 720 = true := by
  have hs : count720 q = (countLit q [-26, -28, -30]) + (countLit q [-31, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30]) (l₂ := [-31, -33, -35])
  have hm := merge_right (literal (valuationOf q) (717)) (literal (valuationOf q) (720)) (countLit q [-26, -28, -30]) (countLit q [-31, -33, -35]) (count720 q) 1 (meaning717 q) (meaning720 q) hs
  change valuationOf q 717 = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 717 = false ∨ valuation q 720 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 718 = false ∨ valuationOf q 721 = true := by
  have hs : count720 q = (countLit q [-26, -28, -30]) + (countLit q [-31, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30]) (l₂ := [-31, -33, -35])
  have hm := merge_right (literal (valuationOf q) (718)) (literal (valuationOf q) (721)) (countLit q [-26, -28, -30]) (countLit q [-31, -33, -35]) (count720 q) 2 (meaning718 q) (meaning721 q) hs
  change valuationOf q 718 = false ∨ valuationOf q 721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 718 = false ∨ valuation q 721 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 712 = false ∨ valuationOf q 720 = true := by
  have hs : count720 q = (countLit q [-26, -28, -30]) + (countLit q [-31, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30]) (l₂ := [-31, -33, -35])
  have hm := merge_left (literal (valuationOf q) (712)) (literal (valuationOf q) (720)) (countLit q [-26, -28, -30]) (countLit q [-31, -33, -35]) (count720 q) 1 (meaning712 q) (meaning720 q) hs
  change valuationOf q 712 = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 712 = false ∨ valuation q 720 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 712 = false ∨ valuationOf q 717 = false ∨ valuationOf q 721 = true := by
  have hs : count720 q = (countLit q [-26, -28, -30]) + (countLit q [-31, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30]) (l₂ := [-31, -33, -35])
  have hm := merge_two (literal (valuationOf q) (712)) (literal (valuationOf q) (717)) (literal (valuationOf q) (721)) (countLit q [-26, -28, -30]) (countLit q [-31, -33, -35]) (count720 q) 1 1 (meaning712 q) (meaning717 q) (meaning721 q) hs
  change valuationOf q 712 = false ∨ valuationOf q 717 = false ∨ valuationOf q 721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 712 = false ∨ valuation q 717 = false ∨ valuation q 721 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 712 = false ∨ valuationOf q 718 = false ∨ valuationOf q 722 = true := by
  have hs : count720 q = (countLit q [-26, -28, -30]) + (countLit q [-31, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30]) (l₂ := [-31, -33, -35])
  have hm := merge_two (literal (valuationOf q) (712)) (literal (valuationOf q) (718)) (literal (valuationOf q) (722)) (countLit q [-26, -28, -30]) (countLit q [-31, -33, -35]) (count720 q) 1 2 (meaning712 q) (meaning718 q) (meaning722 q) hs
  change valuationOf q 712 = false ∨ valuationOf q 718 = false ∨ valuationOf q 722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 712 = false ∨ valuation q 718 = false ∨ valuation q 722 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 713 = false ∨ valuationOf q 721 = true := by
  have hs : count720 q = (countLit q [-26, -28, -30]) + (countLit q [-31, -33, -35]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30]) (l₂ := [-31, -33, -35])
  have hm := merge_left (literal (valuationOf q) (713)) (literal (valuationOf q) (721)) (countLit q [-26, -28, -30]) (countLit q [-31, -33, -35]) (count720 q) 2 (meaning713 q) (meaning721 q) hs
  change valuationOf q 713 = false ∨ valuationOf q 721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 713 = false ∨ valuation q 721 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 726 = true := by
  have hs : count726 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (726)) (countLit q [-39]) (countLit q [-41]) (count726 q) 1 (meaningNeg41 q) (meaning726 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 726 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 726 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 726 = true := by
  have hs : count726 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (726)) (countLit q [-39]) (countLit q [-41]) (count726 q) 1 (meaningNeg39 q) (meaning726 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 726 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 726 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 41 = true ∨ valuationOf q 727 = true := by
  have hs : count726 q = (countLit q [-39]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (727)) (countLit q [-39]) (countLit q [-41]) (count726 q) 1 1 (meaningNeg39 q) (meaningNeg41 q) (meaning727 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 41 = true ∨ valuation q 727 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 726 = false ∨ valuationOf q 728 = true := by
  have hs : count728 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (726)) (literal (valuationOf q) (728)) (countLit q [-37]) (countLit q [-39, -41]) (count728 q) 1 (meaning726 q) (meaning728 q) hs
  change valuationOf q 726 = false ∨ valuationOf q 728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 726 = false ∨ valuation q 728 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 727 = false ∨ valuationOf q 729 = true := by
  have hs : count728 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_right (literal (valuationOf q) (727)) (literal (valuationOf q) (729)) (countLit q [-37]) (countLit q [-39, -41]) (count728 q) 2 (meaning727 q) (meaning729 q) hs
  change valuationOf q 727 = false ∨ valuationOf q 729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 727 = false ∨ valuation q 729 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 728 = true := by
  have hs : count728 q = (countLit q [-37]) + (countLit q [-39, -41]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39, -41])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (728)) (countLit q [-37]) (countLit q [-39, -41]) (count728 q) 1 (meaningNeg37 q) (meaning728 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 728 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 728 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 731 = true := by
  have hs : count731 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (731)) (countLit q [-45]) (countLit q [-46]) (count731 q) 1 (meaningNeg46 q) (meaning731 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 731 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 731 = true := by
  have hs : count731 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (731)) (countLit q [-45]) (countLit q [-46]) (count731 q) 1 (meaningNeg45 q) (meaning731 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 731 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 733 = true := by
  have hs : count733 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (731)) (literal (valuationOf q) (733)) (countLit q [-43]) (countLit q [-45, -46]) (count733 q) 1 (meaning731 q) (meaning733 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 733 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 733 = true := by
  have hs : count733 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (733)) (countLit q [-43]) (countLit q [-45, -46]) (count733 q) 1 (meaningNeg43 q) (meaning733 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 733 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 731 = false ∨ valuationOf q 734 = true := by
  have hs : count733 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (731)) (literal (valuationOf q) (734)) (countLit q [-43]) (countLit q [-45, -46]) (count733 q) 1 1 (meaningNeg43 q) (meaning731 q) (meaning734 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 731 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 731 = false ∨ valuation q 734 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 733 = false ∨ valuationOf q 736 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (733)) (literal (valuationOf q) (736)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 1 (meaning733 q) (meaning736 q) hs
  change valuationOf q 733 = false ∨ valuationOf q 736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 733 = false ∨ valuation q 736 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E147.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112147
