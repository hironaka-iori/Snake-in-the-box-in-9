import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-30, -33, -34]) + (countLit q [-35, -37, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34]) (l₂ := [-35, -37, -41, -42])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (861)) (literal (valuationOf q) (868)) (countLit q [-30, -33, -34]) (countLit q [-35, -37, -41, -42]) (count864 q) 3 2 (meaning855 q) (meaning861 q) (meaning868 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 861 = false ∨ valuation q 868 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 863 = false ∨ valuationOf q 870 = true := by
  have hs : count864 q = (countLit q [-30, -33, -34]) + (countLit q [-35, -37, -41, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34]) (l₂ := [-35, -37, -41, -42])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (863)) (literal (valuationOf q) (870)) (countLit q [-30, -33, -34]) (countLit q [-35, -37, -41, -42]) (count864 q) 3 4 (meaning855 q) (meaning863 q) (meaning870 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 863 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 863 = false ∨ valuation q 870 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 45 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (872)) (countLit q [-43]) (countLit q [-45]) (count871 q) 1 1 (meaningNeg43 q) (meaningNeg45 q) (meaning872 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 872 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (873)) (countLit q [-47]) (countLit q [-48]) (count873 q) 1 (meaningNeg48 q) (meaning873 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 873 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (873)) (countLit q [-47]) (countLit q [-48]) (count873 q) 1 (meaningNeg47 q) (meaning873 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 873 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 48 = true ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (874)) (countLit q [-47]) (countLit q [-48]) (count873 q) 1 1 (meaningNeg47 q) (meaningNeg48 q) (meaning874 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 874 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-43, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-43, -45]) (countLit q [-47, -48]) (count875 q) 2 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-43, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-43, -45]) (countLit q [-47, -48]) (count875 q) 2 1 (meaning872 q) (meaning873 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 873 = false ∨ valuation q 877 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-43, -45]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -45]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-43, -45]) (countLit q [-47, -48]) (count875 q) 2 2 (meaning872 q) (meaning874 q) (meaning878 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = false ∨ valuation q 878 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (879)) (countLit q [-49]) (countLit q [-52]) (count879 q) 1 (meaningNeg52 q) (meaning879 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 879 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (879)) (countLit q [-49]) (countLit q [-52]) (count879 q) 1 (meaningNeg49 q) (meaning879 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 879 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 52 = true ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (880)) (countLit q [-49]) (countLit q [-52]) (count879 q) 1 1 (meaningNeg49 q) (meaningNeg52 q) (meaning880 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 52 = true ∨ valuation q 880 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (881)) (countLit q [-53]) (countLit q [-55]) (count881 q) 1 (meaningNeg55 q) (meaning881 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 881 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (881)) (countLit q [-53]) (countLit q [-55]) (count881 q) 1 (meaningNeg53 q) (meaning881 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 881 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 55 = true ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (882)) (countLit q [-53]) (countLit q [-55]) (count881 q) 1 1 (meaningNeg53 q) (meaningNeg55 q) (meaning882 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 882 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (883)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 1 (meaning881 q) (meaning883 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 883 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (884)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 2 (meaning882 q) (meaning884 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 884 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (879)) (literal (valuationOf q) (883)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 1 (meaning879 q) (meaning883 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 883 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 881 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (881)) (literal (valuationOf q) (884)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 1 1 (meaning879 q) (meaning881 q) (meaning884 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 881 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 881 = false ∨ valuation q 884 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 882 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (882)) (literal (valuationOf q) (885)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 1 2 (meaning879 q) (meaning882 q) (meaning885 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 882 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 882 = false ∨ valuation q 885 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (880)) (literal (valuationOf q) (884)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 2 (meaning880 q) (meaning884 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 884 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 881 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (881)) (literal (valuationOf q) (885)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 2 1 (meaning880 q) (meaning881 q) (meaning885 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 881 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 881 = false ∨ valuation q 885 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 882 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-49, -52]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -52]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (882)) (literal (valuationOf q) (886)) (countLit q [-49, -52]) (countLit q [-53, -55]) (count883 q) 2 2 (meaning880 q) (meaning882 q) (meaning886 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 882 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 882 = false ∨ valuation q 886 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_left (literal (valuationOf q) (876)) (literal (valuationOf q) (888)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 2 (meaning876 q) (meaning888 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 888 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (literal (valuationOf q) (889)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 2 1 (meaning876 q) (meaning883 q) (meaning889 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 883 = false ∨ valuation q 889 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (884)) (literal (valuationOf q) (890)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 2 2 (meaning876 q) (meaning884 q) (meaning890 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 884 = false ∨ valuation q 890 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 885 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (885)) (literal (valuationOf q) (891)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 2 3 (meaning876 q) (meaning885 q) (meaning891 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 885 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 885 = false ∨ valuation q 891 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 886 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (886)) (literal (valuationOf q) (892)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 2 4 (meaning876 q) (meaning886 q) (meaning892 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 886 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 886 = false ∨ valuation q 892 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_left (literal (valuationOf q) (877)) (literal (valuationOf q) (889)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 3 (meaning877 q) (meaning889 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 889 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (883)) (literal (valuationOf q) (890)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 3 1 (meaning877 q) (meaning883 q) (meaning890 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 883 = false ∨ valuation q 890 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (884)) (literal (valuationOf q) (891)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 3 2 (meaning877 q) (meaning884 q) (meaning891 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 884 = false ∨ valuation q 891 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 885 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (885)) (literal (valuationOf q) (892)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 3 3 (meaning877 q) (meaning885 q) (meaning892 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 885 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 885 = false ∨ valuation q 892 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E081.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112081
