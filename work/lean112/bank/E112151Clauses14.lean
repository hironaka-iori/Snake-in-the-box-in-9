import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 867 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-74, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (867)) (literal (valuationOf q) (870)) (countLit q [-74, -75]) (countLit q [-76, -79]) (count869 q) 1 1 (meaning865 q) (meaning867 q) (meaning870 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 867 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 867 = false ∨ valuation q 870 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 868 = false ∨ valuationOf q 871 = true := by
  have hs : count869 q = (countLit q [-74, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (868)) (literal (valuationOf q) (871)) (countLit q [-74, -75]) (countLit q [-76, -79]) (count869 q) 1 2 (meaning865 q) (meaning868 q) (meaning871 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 868 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 868 = false ∨ valuation q 871 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-74, -75]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-76, -79])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-74, -75]) (countLit q [-76, -79]) (count869 q) 2 (meaning866 q) (meaning870 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 870 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_left (literal (valuationOf q) (862)) (literal (valuationOf q) (873)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 1 (meaning862 q) (meaning873 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 873 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 869 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (869)) (literal (valuationOf q) (874)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 1 1 (meaning862 q) (meaning869 q) (meaning874 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 869 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 869 = false ∨ valuation q 874 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 870 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (870)) (literal (valuationOf q) (875)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 1 2 (meaning862 q) (meaning870 q) (meaning875 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 870 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 870 = false ∨ valuation q 875 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 871 = false ∨ valuationOf q 876 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (871)) (literal (valuationOf q) (876)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 1 3 (meaning862 q) (meaning871 q) (meaning876 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 871 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 871 = false ∨ valuation q 876 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_left (literal (valuationOf q) (863)) (literal (valuationOf q) (874)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 2 (meaning863 q) (meaning874 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 874 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 869 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (869)) (literal (valuationOf q) (875)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 2 1 (meaning863 q) (meaning869 q) (meaning875 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 869 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 869 = false ∨ valuation q 875 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 870 = false ∨ valuationOf q 876 = true := by
  have hs : count873 q = (countLit q [-67, -70, -72]) + (countLit q [-74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-67, -70, -72]) (l₂ := [-74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (870)) (literal (valuationOf q) (876)) (countLit q [-67, -70, -72]) (countLit q [-74, -75, -76, -79]) (count873 q) 2 2 (meaning863 q) (meaning870 q) (meaning876 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 870 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 870 = false ∨ valuation q 876 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 880 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (880)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 1 (meaning873 q) (meaning880 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 880 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 881 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (881)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 2 (meaning874 q) (meaning881 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 881 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_right (literal (valuationOf q) (875)) (literal (valuationOf q) (882)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 3 (meaning875 q) (meaning882 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 882 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 883 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_right (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 4 (meaning876 q) (meaning883 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 883 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 873 = false ∨ valuationOf q 881 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (873)) (literal (valuationOf q) (881)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 1 1 (meaning854 q) (meaning873 q) (meaning881 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 873 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 873 = false ∨ valuation q 881 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 874 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (874)) (literal (valuationOf q) (882)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 1 2 (meaning854 q) (meaning874 q) (meaning882 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 874 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 874 = false ∨ valuation q 882 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 875 = false ∨ valuationOf q 883 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (875)) (literal (valuationOf q) (883)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 1 3 (meaning854 q) (meaning875 q) (meaning883 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 875 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 875 = false ∨ valuation q 883 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 873 = false ∨ valuationOf q 882 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (873)) (literal (valuationOf q) (882)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 2 1 (meaning855 q) (meaning873 q) (meaning882 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 873 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 873 = false ∨ valuation q 882 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 874 = false ∨ valuationOf q 883 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (874)) (literal (valuationOf q) (883)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 2 2 (meaning855 q) (meaning874 q) (meaning883 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 874 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 874 = false ∨ valuation q 883 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 875 = false ∨ valuationOf q 884 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (875)) (literal (valuationOf q) (884)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 2 3 (meaning855 q) (meaning875 q) (meaning884 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 875 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 875 = false ∨ valuation q 884 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 874 = false ∨ valuationOf q 884 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (874)) (literal (valuationOf q) (884)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 3 2 (meaning856 q) (meaning874 q) (meaning884 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 874 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 874 = false ∨ valuation q 884 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 875 = false ∨ valuationOf q 885 = true := by
  have hs : count880 q = (countLit q [-56, -58, -59, -62, -63, -64]) + (countLit q [-67, -70, -72, -74, -75, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -62, -63, -64]) (l₂ := [-67, -70, -72, -74, -75, -76, -79])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (875)) (literal (valuationOf q) (885)) (countLit q [-56, -58, -59, -62, -63, -64]) (countLit q [-67, -70, -72, -74, -75, -76, -79]) (count880 q) 3 3 (meaning856 q) (meaning875 q) (meaning885 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 875 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 875 = false ∨ valuation q 885 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-83]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (893)) (countLit q [-83]) (countLit q [-87]) (count893 q) 1 (meaningNeg87 q) (meaning893 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 893 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-83]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (893)) (countLit q [-83]) (countLit q [-87]) (count893 q) 1 (meaningNeg83 q) (meaning893 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 893 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 87 = true ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-83]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (894)) (countLit q [-83]) (countLit q [-87]) (count893 q) 1 1 (meaningNeg83 q) (meaningNeg87 q) (meaning894 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 87 = true ∨ valuation q 894 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_right (literal (valuationOf q) (893)) (literal (valuationOf q) (895)) (countLit q [-80]) (countLit q [-83, -87]) (count895 q) 1 (meaning893 q) (meaning895 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 895 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_right (literal (valuationOf q) (894)) (literal (valuationOf q) (896)) (countLit q [-80]) (countLit q [-83, -87]) (count895 q) 2 (meaning894 q) (meaning896 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 896 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (895)) (countLit q [-80]) (countLit q [-83, -87]) (count895 q) 1 (meaningNeg80 q) (meaning895 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 895 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (893)) (literal (valuationOf q) (896)) (countLit q [-80]) (countLit q [-83, -87]) (count895 q) 1 1 (meaningNeg80 q) (meaning893 q) (meaning896 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 893 = false ∨ valuation q 896 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 894 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-80]) + (countLit q [-83, -87]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-83, -87])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (894)) (literal (valuationOf q) (897)) (countLit q [-80]) (countLit q [-83, -87]) (count895 q) 1 2 (meaningNeg80 q) (meaning894 q) (meaning897 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 894 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 894 = false ∨ valuation q 897 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 898 = true := by
  have hs : count898 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (898)) (countLit q [-89]) (countLit q [-90]) (count898 q) 1 (meaningNeg90 q) (meaning898 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 898 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 898 = true := by
  have hs : count898 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (898)) (countLit q [-89]) (countLit q [-90]) (count898 q) 1 (meaningNeg89 q) (meaning898 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 898 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E151.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112151
