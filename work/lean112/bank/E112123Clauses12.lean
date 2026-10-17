import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 767 = false ∨ valuationOf q 772 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (767)) (literal (valuationOf q) (772)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 1 2 (meaning759 q) (meaning767 q) (meaning772 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 767 = false ∨ valuationOf q 772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 767 = false ∨ valuation q 772 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 768 = false ∨ valuationOf q 773 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (768)) (literal (valuationOf q) (773)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 1 3 (meaning759 q) (meaning768 q) (meaning773 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 768 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 768 = false ∨ valuation q 773 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 769 = false ∨ valuationOf q 774 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (769)) (literal (valuationOf q) (774)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 1 4 (meaning759 q) (meaning769 q) (meaning774 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 769 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 769 = false ∨ valuation q 774 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 771 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_left (literal (valuationOf q) (760)) (literal (valuationOf q) (771)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 2 (meaning760 q) (meaning771 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 771 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 766 = false ∨ valuationOf q 772 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (766)) (literal (valuationOf q) (772)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 2 1 (meaning760 q) (meaning766 q) (meaning772 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 766 = false ∨ valuationOf q 772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 766 = false ∨ valuation q 772 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 767 = false ∨ valuationOf q 773 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (767)) (literal (valuationOf q) (773)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 2 2 (meaning760 q) (meaning767 q) (meaning773 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 767 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 767 = false ∨ valuation q 773 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 768 = false ∨ valuationOf q 774 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (768)) (literal (valuationOf q) (774)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 2 3 (meaning760 q) (meaning768 q) (meaning774 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 768 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 768 = false ∨ valuation q 774 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 769 = false ∨ valuationOf q 775 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (769)) (literal (valuationOf q) (775)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 2 4 (meaning760 q) (meaning769 q) (meaning775 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 769 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 769 = false ∨ valuation q 775 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 772 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_left (literal (valuationOf q) (761)) (literal (valuationOf q) (772)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 3 (meaning761 q) (meaning772 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 772 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 766 = false ∨ valuationOf q 773 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (761)) (literal (valuationOf q) (766)) (literal (valuationOf q) (773)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 3 1 (meaning761 q) (meaning766 q) (meaning773 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 766 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 766 = false ∨ valuation q 773 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 767 = false ∨ valuationOf q 774 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (761)) (literal (valuationOf q) (767)) (literal (valuationOf q) (774)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 3 2 (meaning761 q) (meaning767 q) (meaning774 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 767 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 767 = false ∨ valuation q 774 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 768 = false ∨ valuationOf q 775 = true := by
  have hs : count770 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (761)) (literal (valuationOf q) (768)) (literal (valuationOf q) (775)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count770 q) 3 3 (meaning761 q) (meaning768 q) (meaning775 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 768 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 768 = false ∨ valuation q 775 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 777 = true := by
  have hs : count777 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (777)) (countLit q [-17]) (countLit q [-18]) (count777 q) 1 (meaningNeg18 q) (meaning777 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 777 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 777 = true := by
  have hs : count777 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (777)) (countLit q [-17]) (countLit q [-18]) (count777 q) 1 (meaningNeg17 q) (meaning777 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 777 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 18 = true ∨ valuationOf q 778 = true := by
  have hs : count777 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (778)) (countLit q [-17]) (countLit q [-18]) (count777 q) 1 1 (meaningNeg17 q) (meaningNeg18 q) (meaning778 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 778 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 777 = false ∨ valuationOf q 779 = true := by
  have hs : count779 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (777)) (literal (valuationOf q) (779)) (countLit q [-15]) (countLit q [-17, -18]) (count779 q) 1 (meaning777 q) (meaning779 q) hs
  change valuationOf q 777 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 777 = false ∨ valuation q 779 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 778 = false ∨ valuationOf q 780 = true := by
  have hs : count779 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (778)) (literal (valuationOf q) (780)) (countLit q [-15]) (countLit q [-17, -18]) (count779 q) 2 (meaning778 q) (meaning780 q) hs
  change valuationOf q 778 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 778 = false ∨ valuation q 780 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 779 = true := by
  have hs : count779 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (779)) (countLit q [-15]) (countLit q [-17, -18]) (count779 q) 1 (meaningNeg15 q) (meaning779 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 779 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 777 = false ∨ valuationOf q 780 = true := by
  have hs : count779 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (777)) (literal (valuationOf q) (780)) (countLit q [-15]) (countLit q [-17, -18]) (count779 q) 1 1 (meaningNeg15 q) (meaning777 q) (meaning780 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 777 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 777 = false ∨ valuation q 780 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 778 = false ∨ valuationOf q 781 = true := by
  have hs : count779 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (778)) (literal (valuationOf q) (781)) (countLit q [-15]) (countLit q [-17, -18]) (count779 q) 1 2 (meaningNeg15 q) (meaning778 q) (meaning781 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 778 = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 778 = false ∨ valuation q 781 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 782 = true := by
  have hs : count782 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (782)) (countLit q [-20]) (countLit q [-21]) (count782 q) 1 (meaningNeg21 q) (meaning782 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 782 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 782 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 782 = true := by
  have hs : count782 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (782)) (countLit q [-20]) (countLit q [-21]) (count782 q) 1 (meaningNeg20 q) (meaning782 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 782 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 782 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 783 = true := by
  have hs : count782 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (783)) (countLit q [-20]) (countLit q [-21]) (count782 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning783 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 783 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 784 = true := by
  have hs : count784 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (784)) (countLit q [-24]) (countLit q [-25]) (count784 q) 1 (meaningNeg25 q) (meaning784 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 784 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 784 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 785 = true := by
  have hs : count784 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (785)) (countLit q [-24]) (countLit q [-25]) (count784 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning785 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 785 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 785 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 784 = false ∨ valuationOf q 786 = true := by
  have hs : count786 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (784)) (literal (valuationOf q) (786)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count786 q) 1 (meaning784 q) (meaning786 q) hs
  change valuationOf q 784 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 784 = false ∨ valuation q 786 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 785 = false ∨ valuationOf q 787 = true := by
  have hs : count786 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (785)) (literal (valuationOf q) (787)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count786 q) 2 (meaning785 q) (meaning787 q) hs
  change valuationOf q 785 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 785 = false ∨ valuation q 787 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 782 = false ∨ valuationOf q 784 = false ∨ valuationOf q 787 = true := by
  have hs : count786 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (782)) (literal (valuationOf q) (784)) (literal (valuationOf q) (787)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count786 q) 1 1 (meaning782 q) (meaning784 q) (meaning787 q) hs
  change valuationOf q 782 = false ∨ valuationOf q 784 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 782 = false ∨ valuation q 784 = false ∨ valuation q 787 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 782 = false ∨ valuationOf q 785 = false ∨ valuationOf q 788 = true := by
  have hs : count786 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (782)) (literal (valuationOf q) (785)) (literal (valuationOf q) (788)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count786 q) 1 2 (meaning782 q) (meaning785 q) (meaning788 q) hs
  change valuationOf q 782 = false ∨ valuationOf q 785 = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 782 = false ∨ valuation q 785 = false ∨ valuation q 788 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 784 = false ∨ valuationOf q 788 = true := by
  have hs : count786 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (783)) (literal (valuationOf q) (784)) (literal (valuationOf q) (788)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count786 q) 2 1 (meaning783 q) (meaning784 q) (meaning788 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 784 = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 784 = false ∨ valuation q 788 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 785 = false ∨ valuationOf q 789 = true := by
  have hs : count786 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (783)) (literal (valuationOf q) (785)) (literal (valuationOf q) (789)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count786 q) 2 2 (meaning783 q) (meaning785 q) (meaning789 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 785 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 785 = false ∨ valuation q 789 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 790 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (786)) (literal (valuationOf q) (790)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 1 (meaning786 q) (meaning790 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 790 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E123.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112123
