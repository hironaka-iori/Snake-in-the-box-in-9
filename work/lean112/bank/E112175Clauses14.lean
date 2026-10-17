import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning308 q) (meaning412 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 412 = true := counterClause449 (baseVal q)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause451 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 715 = true := by
  have hs : count715 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (715)) (countLit q [-3]) (countLit q [-4]) (count715 q) 1 (meaningNeg3 q) (meaning715 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 715 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 715 = false ∨ valuationOf q 717 = true := by
  have hs : count717 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_right (literal (valuationOf q) (715)) (literal (valuationOf q) (717)) (countLit q [-1]) (countLit q [-3, -4]) (count717 q) 1 (meaning715 q) (meaning717 q) hs
  change valuationOf q 715 = false ∨ valuationOf q 717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 715 = false ∨ valuation q 717 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 715 = false ∨ valuationOf q 718 = true := by
  have hs : count717 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (715)) (literal (valuationOf q) (718)) (countLit q [-1]) (countLit q [-3, -4]) (count717 q) 1 1 (meaningNeg1 q) (meaning715 q) (meaning718 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 715 = false ∨ valuationOf q 718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 715 = false ∨ valuation q 718 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 720 = true := by
  have hs : count720 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (720)) (countLit q [-9]) (countLit q [-10]) (count720 q) 1 (meaningNeg10 q) (meaning720 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 720 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 722 = true := by
  have hs : count722 q = (countLit q [-5]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (720)) (literal (valuationOf q) (722)) (countLit q [-5]) (countLit q [-9, -10]) (count722 q) 1 (meaning720 q) (meaning722 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 722 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 722 = false ∨ valuationOf q 725 = true := by
  have hs : count725 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -9, -10])
  have hm := merge_right (literal (valuationOf q) (722)) (literal (valuationOf q) (725)) (countLit q [-1, -3, -4]) (countLit q [-5, -9, -10]) (count725 q) 1 (meaning722 q) (meaning725 q) hs
  change valuationOf q 722 = false ∨ valuationOf q 725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 722 = false ∨ valuation q 725 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 717 = false ∨ valuationOf q 722 = false ∨ valuationOf q 726 = true := by
  have hs : count725 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -9, -10])
  have hm := merge_two (literal (valuationOf q) (717)) (literal (valuationOf q) (722)) (literal (valuationOf q) (726)) (countLit q [-1, -3, -4]) (countLit q [-5, -9, -10]) (count725 q) 1 1 (meaning717 q) (meaning722 q) (meaning726 q) hs
  change valuationOf q 717 = false ∨ valuationOf q 722 = false ∨ valuationOf q 726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 717 = false ∨ valuation q 722 = false ∨ valuation q 726 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 718 = false ∨ valuationOf q 722 = false ∨ valuationOf q 727 = true := by
  have hs : count725 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -9, -10])
  have hm := merge_two (literal (valuationOf q) (718)) (literal (valuationOf q) (722)) (literal (valuationOf q) (727)) (countLit q [-1, -3, -4]) (countLit q [-5, -9, -10]) (count725 q) 2 1 (meaning718 q) (meaning722 q) (meaning727 q) hs
  change valuationOf q 718 = false ∨ valuationOf q 722 = false ∨ valuationOf q 727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 718 = false ∨ valuation q 722 = false ∨ valuation q 727 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 731 = true := by
  have hs : count731 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (731)) (countLit q [-14]) (countLit q [-16]) (count731 q) 1 (meaningNeg14 q) (meaning731 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 731 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 16 = true ∨ valuationOf q 732 = true := by
  have hs : count731 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (732)) (countLit q [-14]) (countLit q [-16]) (count731 q) 1 1 (meaningNeg14 q) (meaningNeg16 q) (meaning732 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 732 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 16 = true ∨ valuation q 732 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 733 = true := by
  have hs : count733 q = (countLit q [-12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -16])
  have hm := merge_right (literal (valuationOf q) (731)) (literal (valuationOf q) (733)) (countLit q [-12]) (countLit q [-14, -16]) (count733 q) 1 (meaning731 q) (meaning733 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 733 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 732 = false ∨ valuationOf q 734 = true := by
  have hs : count733 q = (countLit q [-12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -16])
  have hm := merge_right (literal (valuationOf q) (732)) (literal (valuationOf q) (734)) (countLit q [-12]) (countLit q [-14, -16]) (count733 q) 2 (meaning732 q) (meaning734 q) hs
  change valuationOf q 732 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 732 = false ∨ valuation q 734 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 731 = false ∨ valuationOf q 734 = true := by
  have hs : count733 q = (countLit q [-12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (731)) (literal (valuationOf q) (734)) (countLit q [-12]) (countLit q [-14, -16]) (count733 q) 1 1 (meaningNeg12 q) (meaning731 q) (meaning734 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 731 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 731 = false ∨ valuation q 734 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 732 = false ∨ valuationOf q 735 = true := by
  have hs : count733 q = (countLit q [-12]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (732)) (literal (valuationOf q) (735)) (countLit q [-12]) (countLit q [-14, -16]) (count733 q) 1 2 (meaningNeg12 q) (meaning732 q) (meaning735 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 732 = false ∨ valuationOf q 735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 732 = false ∨ valuation q 735 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 736 = true := by
  have hs : count736 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (736)) (countLit q [-17]) (countLit q [-19]) (count736 q) 1 (meaningNeg19 q) (meaning736 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 736 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 736 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 19 = true ∨ valuationOf q 737 = true := by
  have hs : count736 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (737)) (countLit q [-17]) (countLit q [-19]) (count736 q) 1 1 (meaningNeg17 q) (meaningNeg19 q) (meaning737 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 737 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 737 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 738 = true := by
  have hs : count738 q = (countLit q [-20]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (738)) (countLit q [-20]) (countLit q [-24]) (count738 q) 1 (meaningNeg20 q) (meaning738 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 738 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 738 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 24 = true ∨ valuationOf q 739 = true := by
  have hs : count738 q = (countLit q [-20]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (739)) (countLit q [-20]) (countLit q [-24]) (count738 q) 1 1 (meaningNeg20 q) (meaningNeg24 q) (meaning739 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 739 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 24 = true ∨ valuation q 739 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 736 = false ∨ valuationOf q 739 = false ∨ valuationOf q 742 = true := by
  have hs : count740 q = (countLit q [-17, -19]) + (countLit q [-20, -24]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-20, -24])
  have hm := merge_two (literal (valuationOf q) (736)) (literal (valuationOf q) (739)) (literal (valuationOf q) (742)) (countLit q [-17, -19]) (countLit q [-20, -24]) (count740 q) 1 2 (meaning736 q) (meaning739 q) (meaning742 q) hs
  change valuationOf q 736 = false ∨ valuationOf q 739 = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 736 = false ∨ valuation q 739 = false ∨ valuation q 742 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 738 = false ∨ valuationOf q 742 = true := by
  have hs : count740 q = (countLit q [-17, -19]) + (countLit q [-20, -24]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-20, -24])
  have hm := merge_two (literal (valuationOf q) (737)) (literal (valuationOf q) (738)) (literal (valuationOf q) (742)) (countLit q [-17, -19]) (countLit q [-20, -24]) (count740 q) 2 1 (meaning737 q) (meaning738 q) (meaning742 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 738 = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 738 = false ∨ valuation q 742 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 739 = false ∨ valuationOf q 743 = true := by
  have hs : count740 q = (countLit q [-17, -19]) + (countLit q [-20, -24]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-20, -24])
  have hm := merge_two (literal (valuationOf q) (737)) (literal (valuationOf q) (739)) (literal (valuationOf q) (743)) (countLit q [-17, -19]) (countLit q [-20, -24]) (count740 q) 2 2 (meaning737 q) (meaning739 q) (meaning743 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 739 = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 739 = false ∨ valuation q 743 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 733 = false ∨ valuationOf q 743 = false ∨ valuationOf q 748 = true := by
  have hs : count744 q = (countLit q [-12, -14, -16]) + (countLit q [-17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -16]) (l₂ := [-17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (733)) (literal (valuationOf q) (743)) (literal (valuationOf q) (748)) (countLit q [-12, -14, -16]) (countLit q [-17, -19, -20, -24]) (count744 q) 1 4 (meaning733 q) (meaning743 q) (meaning748 q) hs
  change valuationOf q 733 = false ∨ valuationOf q 743 = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 733 = false ∨ valuation q 743 = false ∨ valuation q 748 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 734 = false ∨ valuationOf q 742 = false ∨ valuationOf q 748 = true := by
  have hs : count744 q = (countLit q [-12, -14, -16]) + (countLit q [-17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -16]) (l₂ := [-17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (734)) (literal (valuationOf q) (742)) (literal (valuationOf q) (748)) (countLit q [-12, -14, -16]) (countLit q [-17, -19, -20, -24]) (count744 q) 2 3 (meaning734 q) (meaning742 q) (meaning748 q) hs
  change valuationOf q 734 = false ∨ valuationOf q 742 = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 734 = false ∨ valuation q 742 = false ∨ valuation q 748 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 734 = false ∨ valuationOf q 743 = false ∨ valuationOf q 749 = true := by
  have hs : count744 q = (countLit q [-12, -14, -16]) + (countLit q [-17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -16]) (l₂ := [-17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (734)) (literal (valuationOf q) (743)) (literal (valuationOf q) (749)) (countLit q [-12, -14, -16]) (countLit q [-17, -19, -20, -24]) (count744 q) 2 4 (meaning734 q) (meaning743 q) (meaning749 q) hs
  change valuationOf q 734 = false ∨ valuationOf q 743 = false ∨ valuationOf q 749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 734 = false ∨ valuation q 743 = false ∨ valuation q 749 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 735 = false ∨ valuationOf q 742 = false ∨ valuationOf q 749 = true := by
  have hs : count744 q = (countLit q [-12, -14, -16]) + (countLit q [-17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -16]) (l₂ := [-17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (735)) (literal (valuationOf q) (742)) (literal (valuationOf q) (749)) (countLit q [-12, -14, -16]) (countLit q [-17, -19, -20, -24]) (count744 q) 3 3 (meaning735 q) (meaning742 q) (meaning749 q) hs
  change valuationOf q 735 = false ∨ valuationOf q 742 = false ∨ valuationOf q 749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 735 = false ∨ valuation q 742 = false ∨ valuation q 749 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 725 = false ∨ valuationOf q 749 = false ∨ valuationOf q 757 = true := by
  have hs : count751 q = (countLit q [-1, -3, -4, -5, -9, -10]) + (countLit q [-12, -14, -16, -17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10]) (l₂ := [-12, -14, -16, -17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (725)) (literal (valuationOf q) (749)) (literal (valuationOf q) (757)) (countLit q [-1, -3, -4, -5, -9, -10]) (countLit q [-12, -14, -16, -17, -19, -20, -24]) (count751 q) 1 6 (meaning725 q) (meaning749 q) (meaning757 q) hs
  change valuationOf q 725 = false ∨ valuationOf q 749 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 725 = false ∨ valuation q 749 = false ∨ valuation q 757 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 726 = false ∨ valuationOf q 748 = false ∨ valuationOf q 757 = true := by
  have hs : count751 q = (countLit q [-1, -3, -4, -5, -9, -10]) + (countLit q [-12, -14, -16, -17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10]) (l₂ := [-12, -14, -16, -17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (726)) (literal (valuationOf q) (748)) (literal (valuationOf q) (757)) (countLit q [-1, -3, -4, -5, -9, -10]) (countLit q [-12, -14, -16, -17, -19, -20, -24]) (count751 q) 2 5 (meaning726 q) (meaning748 q) (meaning757 q) hs
  change valuationOf q 726 = false ∨ valuationOf q 748 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 726 = false ∨ valuation q 748 = false ∨ valuation q 757 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 726 = false ∨ valuationOf q 749 = false ∨ valuationOf q 758 = true := by
  have hs : count751 q = (countLit q [-1, -3, -4, -5, -9, -10]) + (countLit q [-12, -14, -16, -17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10]) (l₂ := [-12, -14, -16, -17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (726)) (literal (valuationOf q) (749)) (literal (valuationOf q) (758)) (countLit q [-1, -3, -4, -5, -9, -10]) (countLit q [-12, -14, -16, -17, -19, -20, -24]) (count751 q) 2 6 (meaning726 q) (meaning749 q) (meaning758 q) hs
  change valuationOf q 726 = false ∨ valuationOf q 749 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 726 = false ∨ valuation q 749 = false ∨ valuation q 758 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 727 = false ∨ valuationOf q 748 = false ∨ valuationOf q 758 = true := by
  have hs : count751 q = (countLit q [-1, -3, -4, -5, -9, -10]) + (countLit q [-12, -14, -16, -17, -19, -20, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10]) (l₂ := [-12, -14, -16, -17, -19, -20, -24])
  have hm := merge_two (literal (valuationOf q) (727)) (literal (valuationOf q) (748)) (literal (valuationOf q) (758)) (countLit q [-1, -3, -4, -5, -9, -10]) (countLit q [-12, -14, -16, -17, -19, -20, -24]) (count751 q) 3 5 (meaning727 q) (meaning748 q) (meaning758 q) hs
  change valuationOf q 727 = false ∨ valuationOf q 748 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 727 = false ∨ valuation q 748 = false ∨ valuation q 758 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 764 = true := by
  have hs : count764 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (764)) (countLit q [-28]) (countLit q [-29]) (count764 q) 1 (meaningNeg29 q) (meaning764 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 764 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E175.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112175
