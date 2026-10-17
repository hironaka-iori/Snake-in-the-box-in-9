import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 834 = false ∨ valuationOf q 846 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (818)) (literal (valuationOf q) (834)) (literal (valuationOf q) (846)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 5 1 (meaning818 q) (meaning834 q) (meaning846 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 834 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 834 = false ∨ valuation q 846 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 835 = false ∨ valuationOf q 847 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (818)) (literal (valuationOf q) (835)) (literal (valuationOf q) (847)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 5 2 (meaning818 q) (meaning835 q) (meaning847 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 835 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 835 = false ∨ valuation q 847 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 836 = false ∨ valuationOf q 848 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (818)) (literal (valuationOf q) (836)) (literal (valuationOf q) (848)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 5 3 (meaning818 q) (meaning836 q) (meaning848 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 836 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 836 = false ∨ valuation q 848 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (855)) (countLit q [-29]) (countLit q [-30]) (count855 q) 1 (meaningNeg30 q) (meaning855 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 855 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (855)) (countLit q [-29]) (countLit q [-30]) (count855 q) 1 (meaningNeg29 q) (meaning855 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 855 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 856 = true := by
  have hs : count855 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (856)) (countLit q [-29]) (countLit q [-30]) (count855 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning856 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 856 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (855)) (literal (valuationOf q) (857)) (countLit q [-27]) (countLit q [-29, -30]) (count857 q) 1 (meaning855 q) (meaning857 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 857 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (countLit q [-27]) (countLit q [-29, -30]) (count857 q) 2 (meaning856 q) (meaning858 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (857)) (countLit q [-27]) (countLit q [-29, -30]) (count857 q) 1 (meaningNeg27 q) (meaning857 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 857 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (855)) (literal (valuationOf q) (858)) (countLit q [-27]) (countLit q [-29, -30]) (count857 q) 1 1 (meaningNeg27 q) (meaning855 q) (meaning858 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 855 = false ∨ valuation q 858 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 856 = false ∨ valuationOf q 859 = true := by
  have hs : count857 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (856)) (literal (valuationOf q) (859)) (countLit q [-27]) (countLit q [-29, -30]) (count857 q) 1 2 (meaningNeg27 q) (meaning856 q) (meaning859 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 856 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 856 = false ∨ valuation q 859 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-32]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (860)) (countLit q [-32]) (countLit q [-36]) (count860 q) 1 (meaningNeg36 q) (meaning860 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 860 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-32]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (860)) (countLit q [-32]) (countLit q [-36]) (count860 q) 1 (meaningNeg32 q) (meaning860 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 860 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 36 = true ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-32]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (861)) (countLit q [-32]) (countLit q [-36]) (count860 q) 1 1 (meaningNeg32 q) (meaningNeg36 q) (meaning861 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 36 = true ∨ valuation q 861 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (862)) (countLit q [-37]) (countLit q [-39]) (count862 q) 1 (meaningNeg39 q) (meaning862 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 862 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 862 = true := by
  have hs : count862 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (862)) (countLit q [-37]) (countLit q [-39]) (count862 q) 1 (meaningNeg37 q) (meaning862 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 862 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 39 = true ∨ valuationOf q 863 = true := by
  have hs : count862 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (863)) (countLit q [-37]) (countLit q [-39]) (count862 q) 1 1 (meaningNeg37 q) (meaningNeg39 q) (meaning863 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 863 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (862)) (literal (valuationOf q) (864)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 1 (meaning862 q) (meaning864 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 864 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 2 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 1 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (862)) (literal (valuationOf q) (865)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 1 1 (meaning860 q) (meaning862 q) (meaning865 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 862 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 862 = false ∨ valuation q 865 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (860)) (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 1 2 (meaning860 q) (meaning863 q) (meaning866 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 863 = false ∨ valuation q 866 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 2 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 862 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (862)) (literal (valuationOf q) (866)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 2 1 (meaning861 q) (meaning862 q) (meaning866 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 862 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 862 = false ∨ valuation q 866 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-32, -36]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -36]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-32, -36]) (countLit q [-37, -39]) (count864 q) 2 2 (meaning861 q) (meaning863 q) (meaning867 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 863 = false ∨ valuation q 867 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_right (literal (valuationOf q) (864)) (literal (valuationOf q) (868)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 1 (meaning864 q) (meaning868 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 868 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_right (literal (valuationOf q) (865)) (literal (valuationOf q) (869)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 2 (meaning865 q) (meaning869 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 869 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_right (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 3 (meaning866 q) (meaning870 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 870 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 871 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_right (literal (valuationOf q) (867)) (literal (valuationOf q) (871)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 4 (meaning867 q) (meaning871 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 871 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (868)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 1 (meaning857 q) (meaning868 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 868 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 864 = false ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (864)) (literal (valuationOf q) (869)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 1 1 (meaning857 q) (meaning864 q) (meaning869 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 864 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 864 = false ∨ valuation q 869 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 865 = false ∨ valuationOf q 870 = true := by
  have hs : count868 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -36, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -36, -37, -39])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (865)) (literal (valuationOf q) (870)) (countLit q [-27, -29, -30]) (countLit q [-32, -36, -37, -39]) (count868 q) 1 2 (meaning857 q) (meaning865 q) (meaning870 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 865 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 865 = false ∨ valuation q 870 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E159.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112159
