import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 734 = false ∨ valuationOf q 737 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (734)) (literal (valuationOf q) (737)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 2 (meaning734 q) (meaning737 q) hs
  change valuationOf q 734 = false ∨ valuationOf q 737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 734 = false ∨ valuation q 737 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 728 = false ∨ valuationOf q 736 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (728)) (literal (valuationOf q) (736)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 1 (meaning728 q) (meaning736 q) hs
  change valuationOf q 728 = false ∨ valuationOf q 736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 728 = false ∨ valuation q 736 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 728 = false ∨ valuationOf q 733 = false ∨ valuationOf q 737 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (728)) (literal (valuationOf q) (733)) (literal (valuationOf q) (737)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 1 1 (meaning728 q) (meaning733 q) (meaning737 q) hs
  change valuationOf q 728 = false ∨ valuationOf q 733 = false ∨ valuationOf q 737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 728 = false ∨ valuation q 733 = false ∨ valuation q 737 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 728 = false ∨ valuationOf q 734 = false ∨ valuationOf q 738 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (728)) (literal (valuationOf q) (734)) (literal (valuationOf q) (738)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 1 2 (meaning728 q) (meaning734 q) (meaning738 q) hs
  change valuationOf q 728 = false ∨ valuationOf q 734 = false ∨ valuationOf q 738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 728 = false ∨ valuation q 734 = false ∨ valuation q 738 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 737 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (729)) (literal (valuationOf q) (737)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 2 (meaning729 q) (meaning737 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 737 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 733 = false ∨ valuationOf q 738 = true := by
  have hs : count736 q = (countLit q [-37, -39, -41]) + (countLit q [-43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-37, -39, -41]) (l₂ := [-43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (733)) (literal (valuationOf q) (738)) (countLit q [-37, -39, -41]) (countLit q [-43, -45, -46]) (count736 q) 2 1 (meaning729 q) (meaning733 q) (meaning738 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 733 = false ∨ valuationOf q 738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 733 = false ∨ valuation q 738 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 736 = false ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (736)) (literal (valuationOf q) (742)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 1 (meaning736 q) (meaning742 q) hs
  change valuationOf q 736 = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 736 = false ∨ valuation q 742 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 743 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (737)) (literal (valuationOf q) (743)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 2 (meaning737 q) (meaning743 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 743 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 738 = false ∨ valuationOf q 744 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_right (literal (valuationOf q) (738)) (literal (valuationOf q) (744)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 3 (meaning738 q) (meaning744 q) hs
  change valuationOf q 738 = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 738 = false ∨ valuation q 744 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (720)) (literal (valuationOf q) (742)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 1 (meaning720 q) (meaning742 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 742 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 736 = false ∨ valuationOf q 743 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (720)) (literal (valuationOf q) (736)) (literal (valuationOf q) (743)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 1 1 (meaning720 q) (meaning736 q) (meaning743 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 736 = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 736 = false ∨ valuation q 743 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 737 = false ∨ valuationOf q 744 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (720)) (literal (valuationOf q) (737)) (literal (valuationOf q) (744)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 1 2 (meaning720 q) (meaning737 q) (meaning744 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 737 = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 737 = false ∨ valuation q 744 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 738 = false ∨ valuationOf q 745 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (720)) (literal (valuationOf q) (738)) (literal (valuationOf q) (745)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 1 3 (meaning720 q) (meaning738 q) (meaning745 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 738 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 738 = false ∨ valuation q 745 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 721 = false ∨ valuationOf q 743 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (721)) (literal (valuationOf q) (743)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 2 (meaning721 q) (meaning743 q) hs
  change valuationOf q 721 = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 721 = false ∨ valuation q 743 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 721 = false ∨ valuationOf q 736 = false ∨ valuationOf q 744 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (721)) (literal (valuationOf q) (736)) (literal (valuationOf q) (744)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 2 1 (meaning721 q) (meaning736 q) (meaning744 q) hs
  change valuationOf q 721 = false ∨ valuationOf q 736 = false ∨ valuationOf q 744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 721 = false ∨ valuation q 736 = false ∨ valuation q 744 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 721 = false ∨ valuationOf q 737 = false ∨ valuationOf q 745 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (721)) (literal (valuationOf q) (737)) (literal (valuationOf q) (745)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 2 2 (meaning721 q) (meaning737 q) (meaning745 q) hs
  change valuationOf q 721 = false ∨ valuationOf q 737 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 721 = false ∨ valuation q 737 = false ∨ valuation q 745 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 722 = false ∨ valuationOf q 736 = false ∨ valuationOf q 745 = true := by
  have hs : count742 q = (countLit q [-26, -28, -30, -31, -33, -35]) + (countLit q [-37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -30, -31, -33, -35]) (l₂ := [-37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (722)) (literal (valuationOf q) (736)) (literal (valuationOf q) (745)) (countLit q [-26, -28, -30, -31, -33, -35]) (countLit q [-37, -39, -41, -43, -45, -46]) (count742 q) 3 1 (meaning722 q) (meaning736 q) (meaning745 q) hs
  change valuationOf q 722 = false ∨ valuationOf q 736 = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 722 = false ∨ valuation q 736 = false ∨ valuation q 745 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 702 = false ∨ valuationOf q 743 = false ∨ valuationOf q 754 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (702)) (literal (valuationOf q) (743)) (literal (valuationOf q) (754)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 2 2 (meaning702 q) (meaning743 q) (meaning754 q) hs
  change valuationOf q 702 = false ∨ valuationOf q 743 = false ∨ valuationOf q 754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 702 = false ∨ valuation q 743 = false ∨ valuation q 754 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 702 = false ∨ valuationOf q 744 = false ∨ valuationOf q 755 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (702)) (literal (valuationOf q) (744)) (literal (valuationOf q) (755)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 2 3 (meaning702 q) (meaning744 q) (meaning755 q) hs
  change valuationOf q 702 = false ∨ valuationOf q 744 = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 702 = false ∨ valuation q 744 = false ∨ valuation q 755 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 702 = false ∨ valuationOf q 745 = false ∨ valuationOf q 756 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (702)) (literal (valuationOf q) (745)) (literal (valuationOf q) (756)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 2 4 (meaning702 q) (meaning745 q) (meaning756 q) hs
  change valuationOf q 702 = false ∨ valuationOf q 745 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 702 = false ∨ valuation q 745 = false ∨ valuation q 756 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 703 = false ∨ valuationOf q 742 = false ∨ valuationOf q 754 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (703)) (literal (valuationOf q) (742)) (literal (valuationOf q) (754)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 3 1 (meaning703 q) (meaning742 q) (meaning754 q) hs
  change valuationOf q 703 = false ∨ valuationOf q 742 = false ∨ valuationOf q 754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 703 = false ∨ valuation q 742 = false ∨ valuation q 754 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 703 = false ∨ valuationOf q 743 = false ∨ valuationOf q 755 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (703)) (literal (valuationOf q) (743)) (literal (valuationOf q) (755)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 3 2 (meaning703 q) (meaning743 q) (meaning755 q) hs
  change valuationOf q 703 = false ∨ valuationOf q 743 = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 703 = false ∨ valuation q 743 = false ∨ valuation q 755 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 703 = false ∨ valuationOf q 744 = false ∨ valuationOf q 756 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (703)) (literal (valuationOf q) (744)) (literal (valuationOf q) (756)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 3 3 (meaning703 q) (meaning744 q) (meaning756 q) hs
  change valuationOf q 703 = false ∨ valuationOf q 744 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 703 = false ∨ valuation q 744 = false ∨ valuation q 756 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 703 = false ∨ valuationOf q 745 = false ∨ valuationOf q 757 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (703)) (literal (valuationOf q) (745)) (literal (valuationOf q) (757)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 3 4 (meaning703 q) (meaning745 q) (meaning757 q) hs
  change valuationOf q 703 = false ∨ valuationOf q 745 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 703 = false ∨ valuation q 745 = false ∨ valuation q 757 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 704 = false ∨ valuationOf q 742 = false ∨ valuationOf q 755 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (704)) (literal (valuationOf q) (742)) (literal (valuationOf q) (755)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 4 1 (meaning704 q) (meaning742 q) (meaning755 q) hs
  change valuationOf q 704 = false ∨ valuationOf q 742 = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 704 = false ∨ valuation q 742 = false ∨ valuation q 755 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 704 = false ∨ valuationOf q 743 = false ∨ valuationOf q 756 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (704)) (literal (valuationOf q) (743)) (literal (valuationOf q) (756)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 4 2 (meaning704 q) (meaning743 q) (meaning756 q) hs
  change valuationOf q 704 = false ∨ valuationOf q 743 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 704 = false ∨ valuation q 743 = false ∨ valuation q 756 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 704 = false ∨ valuationOf q 744 = false ∨ valuationOf q 757 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (704)) (literal (valuationOf q) (744)) (literal (valuationOf q) (757)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 4 3 (meaning704 q) (meaning744 q) (meaning757 q) hs
  change valuationOf q 704 = false ∨ valuationOf q 744 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 704 = false ∨ valuation q 744 = false ∨ valuation q 757 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 755 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_left (literal (valuationOf q) (705)) (literal (valuationOf q) (755)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 5 (meaning705 q) (meaning755 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 755 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 742 = false ∨ valuationOf q 756 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (705)) (literal (valuationOf q) (742)) (literal (valuationOf q) (756)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 5 1 (meaning705 q) (meaning742 q) (meaning756 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 742 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 742 = false ∨ valuation q 756 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 743 = false ∨ valuationOf q 757 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (705)) (literal (valuationOf q) (743)) (literal (valuationOf q) (757)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 5 2 (meaning705 q) (meaning743 q) (meaning757 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 743 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 743 = false ∨ valuation q 757 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 705 = false ∨ valuationOf q 744 = false ∨ valuationOf q 758 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (705)) (literal (valuationOf q) (744)) (literal (valuationOf q) (758)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 5 3 (meaning705 q) (meaning744 q) (meaning758 q) hs
  change valuationOf q 705 = false ∨ valuationOf q 744 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 705 = false ∨ valuation q 744 = false ∨ valuation q 758 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 706 = false ∨ valuationOf q 743 = false ∨ valuationOf q 758 = true := by
  have hs : count751 q = (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) + (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (l₂ := [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46])
  have hm := merge_two (literal (valuationOf q) (706)) (literal (valuationOf q) (743)) (literal (valuationOf q) (758)) (countLit q [-1, -3, -6, -7, -9, -11, -13, -14, -18, -21, -22, -25]) (countLit q [-26, -28, -30, -31, -33, -35, -37, -39, -41, -43, -45, -46]) (count751 q) 6 2 (meaning706 q) (meaning743 q) (meaning758 q) hs
  change valuationOf q 706 = false ∨ valuationOf q 743 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 706 = false ∨ valuation q 743 = false ∨ valuation q 758 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E147.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112147
