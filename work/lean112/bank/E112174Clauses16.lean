import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 703 = false ∨ valuationOf q 705 = true := by
  have hs : count704 q = (countLit q [-10]) + (countLit q [-12, -14]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -14])
  have hm := merge_right (literal (valuationOf q) (703)) (literal (valuationOf q) (705)) (countLit q [-10]) (countLit q [-12, -14]) (count704 q) 2 (meaning703 q) (meaning705 q) hs
  change valuationOf q 703 = false ∨ valuationOf q 705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 703 = false ∨ valuation q 705 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 704 = true := by
  have hs : count704 q = (countLit q [-10]) + (countLit q [-12, -14]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -14])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (704)) (countLit q [-10]) (countLit q [-12, -14]) (count704 q) 1 (meaningNeg10 q) (meaning704 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 704 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 704 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 702 = false ∨ valuationOf q 705 = true := by
  have hs : count704 q = (countLit q [-10]) + (countLit q [-12, -14]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -14])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (702)) (literal (valuationOf q) (705)) (countLit q [-10]) (countLit q [-12, -14]) (count704 q) 1 1 (meaningNeg10 q) (meaning702 q) (meaning705 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 702 = false ∨ valuationOf q 705 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 702 = false ∨ valuation q 705 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 703 = false ∨ valuationOf q 706 = true := by
  have hs : count704 q = (countLit q [-10]) + (countLit q [-12, -14]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12, -14])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (703)) (literal (valuationOf q) (706)) (countLit q [-10]) (countLit q [-12, -14]) (count704 q) 1 2 (meaningNeg10 q) (meaning703 q) (meaning706 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 703 = false ∨ valuationOf q 706 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 703 = false ∨ valuation q 706 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 704 = false ∨ valuationOf q 707 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_right (literal (valuationOf q) (704)) (literal (valuationOf q) (707)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 1 (meaning704 q) (meaning707 q) hs
  change valuationOf q 704 = false ∨ valuationOf q 707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 704 = false ∨ valuation q 707 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 708 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_right (literal (valuationOf q) (705)) (literal (valuationOf q) (708)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 2 (meaning705 q) (meaning708 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 708 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 706 = false ∨ valuationOf q 709 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_right (literal (valuationOf q) (706)) (literal (valuationOf q) (709)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 3 (meaning706 q) (meaning709 q) hs
  change valuationOf q 706 = false ∨ valuationOf q 709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 706 = false ∨ valuation q 709 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 699 = false ∨ valuationOf q 707 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_left (literal (valuationOf q) (699)) (literal (valuationOf q) (707)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 1 (meaning699 q) (meaning707 q) hs
  change valuationOf q 699 = false ∨ valuationOf q 707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 699 = false ∨ valuation q 707 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 699 = false ∨ valuationOf q 704 = false ∨ valuationOf q 708 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_two (literal (valuationOf q) (699)) (literal (valuationOf q) (704)) (literal (valuationOf q) (708)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 1 1 (meaning699 q) (meaning704 q) (meaning708 q) hs
  change valuationOf q 699 = false ∨ valuationOf q 704 = false ∨ valuationOf q 708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 699 = false ∨ valuation q 704 = false ∨ valuation q 708 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 699 = false ∨ valuationOf q 705 = false ∨ valuationOf q 709 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_two (literal (valuationOf q) (699)) (literal (valuationOf q) (705)) (literal (valuationOf q) (709)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 1 2 (meaning699 q) (meaning705 q) (meaning709 q) hs
  change valuationOf q 699 = false ∨ valuationOf q 705 = false ∨ valuationOf q 709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 699 = false ∨ valuation q 705 = false ∨ valuation q 709 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 699 = false ∨ valuationOf q 706 = false ∨ valuationOf q 710 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_two (literal (valuationOf q) (699)) (literal (valuationOf q) (706)) (literal (valuationOf q) (710)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 1 3 (meaning699 q) (meaning706 q) (meaning710 q) hs
  change valuationOf q 699 = false ∨ valuationOf q 706 = false ∨ valuationOf q 710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 699 = false ∨ valuation q 706 = false ∨ valuation q 710 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 700 = false ∨ valuationOf q 705 = false ∨ valuationOf q 710 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_two (literal (valuationOf q) (700)) (literal (valuationOf q) (705)) (literal (valuationOf q) (710)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 2 2 (meaning700 q) (meaning705 q) (meaning710 q) hs
  change valuationOf q 700 = false ∨ valuationOf q 705 = false ∨ valuationOf q 710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 700 = false ∨ valuation q 705 = false ∨ valuation q 710 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 701 = false ∨ valuationOf q 705 = false ∨ valuationOf q 711 = true := by
  have hs : count707 q = (countLit q [-3, -4, -6]) + (countLit q [-10, -12, -14]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-10, -12, -14])
  have hm := merge_two (literal (valuationOf q) (701)) (literal (valuationOf q) (705)) (literal (valuationOf q) (711)) (countLit q [-3, -4, -6]) (countLit q [-10, -12, -14]) (count707 q) 3 2 (meaning701 q) (meaning705 q) (meaning711 q) hs
  change valuationOf q 701 = false ∨ valuationOf q 705 = false ∨ valuationOf q 711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 701 = false ∨ valuation q 705 = false ∨ valuation q 711 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 713 = true := by
  have hs : count713 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (713)) (countLit q [-17]) (countLit q [-18]) (count713 q) 1 (meaningNeg18 q) (meaning713 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 713 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 713 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 713 = false ∨ valuationOf q 715 = true := by
  have hs : count715 q = (countLit q [-16]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (713)) (literal (valuationOf q) (715)) (countLit q [-16]) (countLit q [-17, -18]) (count715 q) 1 (meaning713 q) (meaning715 q) hs
  change valuationOf q 713 = false ∨ valuationOf q 715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 713 = false ∨ valuation q 715 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 715 = true := by
  have hs : count715 q = (countLit q [-16]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (715)) (countLit q [-16]) (countLit q [-17, -18]) (count715 q) 1 (meaningNeg16 q) (meaning715 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 715 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 713 = false ∨ valuationOf q 716 = true := by
  have hs : count715 q = (countLit q [-16]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (713)) (literal (valuationOf q) (716)) (countLit q [-16]) (countLit q [-17, -18]) (count715 q) 1 1 (meaningNeg16 q) (meaning713 q) (meaning716 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 713 = false ∨ valuationOf q 716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 713 = false ∨ valuation q 716 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 718 = true := by
  have hs : count718 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (718)) (countLit q [-22]) (countLit q [-25]) (count718 q) 1 (meaningNeg25 q) (meaning718 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 718 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 718 = true := by
  have hs : count718 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (718)) (countLit q [-22]) (countLit q [-25]) (count718 q) 1 (meaningNeg22 q) (meaning718 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 718 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 718 = false ∨ valuationOf q 720 = true := by
  have hs : count720 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (718)) (literal (valuationOf q) (720)) (countLit q [-21]) (countLit q [-22, -25]) (count720 q) 1 (meaning718 q) (meaning720 q) hs
  change valuationOf q 718 = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 718 = false ∨ valuation q 720 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 720 = true := by
  have hs : count720 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (720)) (countLit q [-21]) (countLit q [-22, -25]) (count720 q) 1 (meaningNeg21 q) (meaning720 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 720 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 718 = false ∨ valuationOf q 721 = true := by
  have hs : count720 q = (countLit q [-21]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (718)) (literal (valuationOf q) (721)) (countLit q [-21]) (countLit q [-22, -25]) (count720 q) 1 1 (meaningNeg21 q) (meaning718 q) (meaning721 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 718 = false ∨ valuationOf q 721 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 718 = false ∨ valuation q 721 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 723 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_right (literal (valuationOf q) (720)) (literal (valuationOf q) (723)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 1 (meaning720 q) (meaning723 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 723 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 721 = false ∨ valuationOf q 724 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_right (literal (valuationOf q) (721)) (literal (valuationOf q) (724)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 2 (meaning721 q) (meaning724 q) hs
  change valuationOf q 721 = false ∨ valuationOf q 724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 721 = false ∨ valuation q 724 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 715 = false ∨ valuationOf q 723 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (715)) (literal (valuationOf q) (723)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 1 (meaning715 q) (meaning723 q) hs
  change valuationOf q 715 = false ∨ valuationOf q 723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 715 = false ∨ valuation q 723 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 715 = false ∨ valuationOf q 720 = false ∨ valuationOf q 724 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (715)) (literal (valuationOf q) (720)) (literal (valuationOf q) (724)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 1 1 (meaning715 q) (meaning720 q) (meaning724 q) hs
  change valuationOf q 715 = false ∨ valuationOf q 720 = false ∨ valuationOf q 724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 715 = false ∨ valuation q 720 = false ∨ valuation q 724 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 715 = false ∨ valuationOf q 721 = false ∨ valuationOf q 725 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (715)) (literal (valuationOf q) (721)) (literal (valuationOf q) (725)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 1 2 (meaning715 q) (meaning721 q) (meaning725 q) hs
  change valuationOf q 715 = false ∨ valuationOf q 721 = false ∨ valuationOf q 725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 715 = false ∨ valuation q 721 = false ∨ valuation q 725 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 716 = false ∨ valuationOf q 724 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (716)) (literal (valuationOf q) (724)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 2 (meaning716 q) (meaning724 q) hs
  change valuationOf q 716 = false ∨ valuationOf q 724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 716 = false ∨ valuation q 724 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 716 = false ∨ valuationOf q 720 = false ∨ valuationOf q 725 = true := by
  have hs : count723 q = (countLit q [-16, -17, -18]) + (countLit q [-21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -18]) (l₂ := [-21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (716)) (literal (valuationOf q) (720)) (literal (valuationOf q) (725)) (countLit q [-16, -17, -18]) (countLit q [-21, -22, -25]) (count723 q) 2 1 (meaning716 q) (meaning720 q) (meaning725 q) hs
  change valuationOf q 716 = false ∨ valuationOf q 720 = false ∨ valuationOf q 725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 716 = false ∨ valuation q 720 = false ∨ valuation q 725 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 723 = false ∨ valuationOf q 729 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_right (literal (valuationOf q) (723)) (literal (valuationOf q) (729)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 1 (meaning723 q) (meaning729 q) hs
  change valuationOf q 723 = false ∨ valuationOf q 729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 723 = false ∨ valuation q 729 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 724 = false ∨ valuationOf q 730 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_right (literal (valuationOf q) (724)) (literal (valuationOf q) (730)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 2 (meaning724 q) (meaning730 q) hs
  change valuationOf q 724 = false ∨ valuationOf q 730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 724 = false ∨ valuation q 730 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 707 = false ∨ valuationOf q 729 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (707)) (literal (valuationOf q) (729)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 1 (meaning707 q) (meaning729 q) hs
  change valuationOf q 707 = false ∨ valuationOf q 729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 707 = false ∨ valuation q 729 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E174.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112174
