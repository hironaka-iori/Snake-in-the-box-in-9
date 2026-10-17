import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 868 = false ∨ valuationOf q 871 = true := by
  have hs : count869 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (868)) (literal (valuationOf q) (871)) (countLit q [-54]) (countLit q [-56, -59]) (count869 q) 1 2 (meaningNeg54 q) (meaning868 q) (meaning871 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 868 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 868 = false ∨ valuation q 871 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 872 = true := by
  have hs : count872 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (872)) (countLit q [-61]) (countLit q [-62]) (count872 q) 1 (meaningNeg62 q) (meaning872 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 872 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 872 = true := by
  have hs : count872 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (872)) (countLit q [-61]) (countLit q [-62]) (count872 q) 1 (meaningNeg61 q) (meaning872 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 872 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 62 = true ∨ valuationOf q 873 = true := by
  have hs : count872 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (873)) (countLit q [-61]) (countLit q [-62]) (count872 q) 1 1 (meaningNeg61 q) (meaningNeg62 q) (meaning873 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 62 = true ∨ valuation q 873 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 874 = true := by
  have hs : count874 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (874)) (countLit q [-64]) (countLit q [-67]) (count874 q) 1 (meaningNeg67 q) (meaning874 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 874 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 874 = true := by
  have hs : count874 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (874)) (countLit q [-64]) (countLit q [-67]) (count874 q) 1 (meaningNeg64 q) (meaning874 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 874 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 67 = true ∨ valuationOf q 875 = true := by
  have hs : count874 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (875)) (countLit q [-64]) (countLit q [-67]) (count874 q) 1 1 (meaningNeg64 q) (meaningNeg67 q) (meaning875 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 875 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 876 = true := by
  have hs : count876 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (876)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count876 q) 1 (meaning874 q) (meaning876 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 876 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 877 = true := by
  have hs : count876 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_right (literal (valuationOf q) (875)) (literal (valuationOf q) (877)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count876 q) 2 (meaning875 q) (meaning877 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 877 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count876 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count876 q) 1 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true := by
  have hs : count876 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (literal (valuationOf q) (877)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count876 q) 1 1 (meaning872 q) (meaning874 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = false ∨ valuation q 877 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count876 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_left (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count876 q) 2 (meaning873 q) (meaning877 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 877 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count876 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_two (literal (valuationOf q) (873)) (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count876 q) 2 1 (meaning873 q) (meaning874 q) (meaning878 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 874 = false ∨ valuation q 878 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 880 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_right (literal (valuationOf q) (876)) (literal (valuationOf q) (880)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 1 (meaning876 q) (meaning880 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 880 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 881 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_right (literal (valuationOf q) (877)) (literal (valuationOf q) (881)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 2 (meaning877 q) (meaning881 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 881 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (882)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 3 (meaning878 q) (meaning882 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 882 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 880 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (880)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 1 (meaning869 q) (meaning880 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 880 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 1 1 (meaning869 q) (meaning876 q) (meaning881 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 876 = false ∨ valuation q 881 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 877 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (877)) (literal (valuationOf q) (882)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 1 2 (meaning869 q) (meaning877 q) (meaning882 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 877 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 877 = false ∨ valuation q 882 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 881 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_left (literal (valuationOf q) (870)) (literal (valuationOf q) (881)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 2 (meaning870 q) (meaning881 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 881 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (876)) (literal (valuationOf q) (882)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 2 1 (meaning870 q) (meaning876 q) (meaning882 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 876 = false ∨ valuation q 882 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 877 = false ∨ valuationOf q 883 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (877)) (literal (valuationOf q) (883)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 2 2 (meaning870 q) (meaning877 q) (meaning883 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 877 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 877 = false ∨ valuation q 883 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_left (literal (valuationOf q) (871)) (literal (valuationOf q) (882)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 3 (meaning871 q) (meaning882 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 882 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 876 = false ∨ valuationOf q 883 = true := by
  have hs : count880 q = (countLit q [-54, -56, -59]) + (countLit q [-61, -62, -64, -67]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59]) (l₂ := [-61, -62, -64, -67])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (countLit q [-54, -56, -59]) (countLit q [-61, -62, -64, -67]) (count880 q) 3 1 (meaning871 q) (meaning876 q) (meaning883 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 876 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 876 = false ∨ valuation q 883 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (887)) (countLit q [-70]) (countLit q [-74]) (count887 q) 1 (meaningNeg74 q) (meaning887 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 887 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (887)) (countLit q [-70]) (countLit q [-74]) (count887 q) 1 (meaningNeg70 q) (meaning887 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 887 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 74 = true ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-70]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (888)) (countLit q [-70]) (countLit q [-74]) (count887 q) 1 1 (meaningNeg70 q) (meaningNeg74 q) (meaning888 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 74 = true ∨ valuation q 888 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 889 = true := by
  have hs : count889 q = (countLit q [-69]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70, -74])
  have hm := merge_right (literal (valuationOf q) (887)) (literal (valuationOf q) (889)) (countLit q [-69]) (countLit q [-70, -74]) (count889 q) 1 (meaning887 q) (meaning889 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 889 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 890 = true := by
  have hs : count889 q = (countLit q [-69]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70, -74])
  have hm := merge_right (literal (valuationOf q) (888)) (literal (valuationOf q) (890)) (countLit q [-69]) (countLit q [-70, -74]) (count889 q) 2 (meaning888 q) (meaning890 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 890 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 889 = true := by
  have hs : count889 q = (countLit q [-69]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70, -74])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (889)) (countLit q [-69]) (countLit q [-70, -74]) (count889 q) 1 (meaningNeg69 q) (meaning889 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 889 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 887 = false ∨ valuationOf q 890 = true := by
  have hs : count889 q = (countLit q [-69]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (887)) (literal (valuationOf q) (890)) (countLit q [-69]) (countLit q [-70, -74]) (count889 q) 1 1 (meaningNeg69 q) (meaning887 q) (meaning890 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 887 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 887 = false ∨ valuation q 890 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 888 = false ∨ valuationOf q 891 = true := by
  have hs : count889 q = (countLit q [-69]) + (countLit q [-70, -74]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70, -74])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (888)) (literal (valuationOf q) (891)) (countLit q [-69]) (countLit q [-70, -74]) (count889 q) 1 2 (meaningNeg69 q) (meaning888 q) (meaning891 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 888 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 888 = false ∨ valuation q 891 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E185.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112185
