import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 834 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (830)) (literal (valuationOf q) (834)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 1 (meaning830 q) (meaning834 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 834 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 835 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (831)) (literal (valuationOf q) (835)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 2 (meaning831 q) (meaning835 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 835 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (832)) (literal (valuationOf q) (836)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 3 (meaning832 q) (meaning836 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 836 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_right (literal (valuationOf q) (833)) (literal (valuationOf q) (837)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 4 (meaning833 q) (meaning837 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 837 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 834 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (823)) (literal (valuationOf q) (834)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 1 (meaning823 q) (meaning834 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 834 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 830 = false ∨ valuationOf q 835 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (830)) (literal (valuationOf q) (835)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 1 1 (meaning823 q) (meaning830 q) (meaning835 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 830 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 830 = false ∨ valuation q 835 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 831 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (831)) (literal (valuationOf q) (836)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 1 2 (meaning823 q) (meaning831 q) (meaning836 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 831 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 831 = false ∨ valuation q 836 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 832 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (832)) (literal (valuationOf q) (837)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 1 3 (meaning823 q) (meaning832 q) (meaning837 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 832 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 832 = false ∨ valuation q 837 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 833 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (833)) (literal (valuationOf q) (838)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 1 4 (meaning823 q) (meaning833 q) (meaning838 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 833 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 833 = false ∨ valuation q 838 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 835 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (824)) (literal (valuationOf q) (835)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 2 (meaning824 q) (meaning835 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 835 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 830 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (824)) (literal (valuationOf q) (830)) (literal (valuationOf q) (836)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 2 1 (meaning824 q) (meaning830 q) (meaning836 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 830 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 830 = false ∨ valuation q 836 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 831 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (824)) (literal (valuationOf q) (831)) (literal (valuationOf q) (837)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 2 2 (meaning824 q) (meaning831 q) (meaning837 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 831 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 831 = false ∨ valuation q 837 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 832 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (824)) (literal (valuationOf q) (832)) (literal (valuationOf q) (838)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 2 3 (meaning824 q) (meaning832 q) (meaning838 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 832 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 832 = false ∨ valuation q 838 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_left (literal (valuationOf q) (825)) (literal (valuationOf q) (836)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 3 (meaning825 q) (meaning836 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 836 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 830 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (825)) (literal (valuationOf q) (830)) (literal (valuationOf q) (837)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 3 1 (meaning825 q) (meaning830 q) (meaning837 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 830 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 830 = false ∨ valuation q 837 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 831 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-12, -14, -15]) + (countLit q [-18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-12, -14, -15]) (l₂ := [-18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (825)) (literal (valuationOf q) (831)) (literal (valuationOf q) (838)) (countLit q [-12, -14, -15]) (countLit q [-18, -21, -23, -24]) (count834 q) 3 2 (meaning825 q) (meaning831 q) (meaning838 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 831 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 831 = false ∨ valuation q 838 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 835 = false ∨ valuationOf q 843 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (835)) (literal (valuationOf q) (843)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 1 2 (meaning814 q) (meaning835 q) (meaning843 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 835 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 835 = false ∨ valuation q 843 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 834 = false ∨ valuationOf q 843 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (834)) (literal (valuationOf q) (843)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 2 1 (meaning815 q) (meaning834 q) (meaning843 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 834 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 834 = false ∨ valuation q 843 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 835 = false ∨ valuationOf q 844 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (835)) (literal (valuationOf q) (844)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 2 2 (meaning815 q) (meaning835 q) (meaning844 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 835 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 835 = false ∨ valuation q 844 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 836 = false ∨ valuationOf q 845 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (836)) (literal (valuationOf q) (845)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 2 3 (meaning815 q) (meaning836 q) (meaning845 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 836 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 836 = false ∨ valuation q 845 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 837 = false ∨ valuationOf q 846 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (837)) (literal (valuationOf q) (846)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 2 4 (meaning815 q) (meaning837 q) (meaning846 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 837 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 837 = false ∨ valuation q 846 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 838 = false ∨ valuationOf q 847 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (838)) (literal (valuationOf q) (847)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 2 5 (meaning815 q) (meaning838 q) (meaning847 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 838 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 838 = false ∨ valuation q 847 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 834 = false ∨ valuationOf q 844 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (834)) (literal (valuationOf q) (844)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 3 1 (meaning816 q) (meaning834 q) (meaning844 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 834 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 834 = false ∨ valuation q 844 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 835 = false ∨ valuationOf q 845 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (835)) (literal (valuationOf q) (845)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 3 2 (meaning816 q) (meaning835 q) (meaning845 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 835 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 835 = false ∨ valuation q 845 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 836 = false ∨ valuationOf q 846 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (836)) (literal (valuationOf q) (846)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 3 3 (meaning816 q) (meaning836 q) (meaning846 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 836 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 836 = false ∨ valuation q 846 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 837 = false ∨ valuationOf q 847 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (837)) (literal (valuationOf q) (847)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 3 4 (meaning816 q) (meaning837 q) (meaning847 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 837 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 837 = false ∨ valuation q 847 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 838 = false ∨ valuationOf q 848 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (838)) (literal (valuationOf q) (848)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 3 5 (meaning816 q) (meaning838 q) (meaning848 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 838 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 838 = false ∨ valuation q 848 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 834 = false ∨ valuationOf q 845 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (817)) (literal (valuationOf q) (834)) (literal (valuationOf q) (845)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 4 1 (meaning817 q) (meaning834 q) (meaning845 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 834 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 834 = false ∨ valuation q 845 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 835 = false ∨ valuationOf q 846 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (817)) (literal (valuationOf q) (835)) (literal (valuationOf q) (846)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 4 2 (meaning817 q) (meaning835 q) (meaning846 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 835 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 835 = false ∨ valuation q 846 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 836 = false ∨ valuationOf q 847 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (817)) (literal (valuationOf q) (836)) (literal (valuationOf q) (847)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 4 3 (meaning817 q) (meaning836 q) (meaning847 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 836 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 836 = false ∨ valuation q 847 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 837 = false ∨ valuationOf q 848 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (817)) (literal (valuationOf q) (837)) (literal (valuationOf q) (848)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 4 4 (meaning817 q) (meaning837 q) (meaning848 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 837 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 837 = false ∨ valuation q 848 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 838 = false ∨ valuationOf q 849 = true := by
  have hs : count841 q = (countLit q [-1, -3, -4, -5, -7, -9, -10]) + (countLit q [-12, -14, -15, -18, -21, -23, -24]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10]) (l₂ := [-12, -14, -15, -18, -21, -23, -24])
  have hm := merge_two (literal (valuationOf q) (817)) (literal (valuationOf q) (838)) (literal (valuationOf q) (849)) (countLit q [-1, -3, -4, -5, -7, -9, -10]) (countLit q [-12, -14, -15, -18, -21, -23, -24]) (count841 q) 4 5 (meaning817 q) (meaning838 q) (meaning849 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 838 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 838 = false ∨ valuation q 849 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E159.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112159
