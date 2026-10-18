import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (866)) (countLit q [-20]) (countLit q [-21]) (count865 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning866 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 866 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-14, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -18]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (865)) (literal (valuationOf q) (867)) (countLit q [-14, -18]) (countLit q [-20, -21]) (count867 q) 1 (meaning865 q) (meaning867 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 867 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-14, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -18]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (866)) (literal (valuationOf q) (868)) (countLit q [-14, -18]) (countLit q [-20, -21]) (count867 q) 2 (meaning866 q) (meaning868 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 868 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-14, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -18]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-14, -18]) (countLit q [-20, -21]) (count867 q) 1 (meaning863 q) (meaning867 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 867 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = false ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-14, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -18]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (literal (valuationOf q) (868)) (countLit q [-14, -18]) (countLit q [-20, -21]) (count867 q) 1 1 (meaning863 q) (meaning865 q) (meaning868 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = false ∨ valuation q 868 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 866 = false ∨ valuationOf q 869 = true := by
  have hs : count867 q = (countLit q [-14, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -18]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (literal (valuationOf q) (869)) (countLit q [-14, -18]) (countLit q [-20, -21]) (count867 q) 1 2 (meaning863 q) (meaning866 q) (meaning869 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 866 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 866 = false ∨ valuation q 869 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-14, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-14, -18]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (864)) (literal (valuationOf q) (868)) (countLit q [-14, -18]) (countLit q [-20, -21]) (count867 q) 2 (meaning864 q) (meaning868 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 868 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (871)) (countLit q [-23]) (countLit q [-24]) (count871 q) 1 (meaningNeg24 q) (meaning871 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 871 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (871)) (countLit q [-23]) (countLit q [-24]) (count871 q) 1 (meaningNeg23 q) (meaning871 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 871 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (872)) (countLit q [-23]) (countLit q [-24]) (count871 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning872 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 872 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (873)) (countLit q [-27]) (countLit q [-29]) (count873 q) 1 (meaningNeg29 q) (meaning873 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 873 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (873)) (countLit q [-27]) (countLit q [-29]) (count873 q) 1 (meaningNeg27 q) (meaning873 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 873 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 29 = true ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (874)) (countLit q [-27]) (countLit q [-29]) (count873 q) 1 1 (meaningNeg27 q) (meaningNeg29 q) (meaning874 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 874 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (875)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count875 q) 1 (meaning873 q) (meaning875 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 875 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (876)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count875 q) 2 (meaning874 q) (meaning876 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 876 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count875 q) 1 (meaning871 q) (meaning875 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 875 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (literal (valuationOf q) (876)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count875 q) 1 1 (meaning871 q) (meaning873 q) (meaning876 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = false ∨ valuation q 876 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count875 q) 2 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count875 q) 2 1 (meaning872 q) (meaning873 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 873 = false ∨ valuation q 877 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_right (literal (valuationOf q) (875)) (literal (valuationOf q) (879)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 1 (meaning875 q) (meaning879 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 879 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_right (literal (valuationOf q) (876)) (literal (valuationOf q) (880)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 2 (meaning876 q) (meaning880 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 880 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (879)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 1 (meaning867 q) (meaning879 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 879 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (875)) (literal (valuationOf q) (880)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 1 1 (meaning867 q) (meaning875 q) (meaning880 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 875 = false ∨ valuation q 880 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 1 2 (meaning867 q) (meaning876 q) (meaning881 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 876 = false ∨ valuation q 881 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 877 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (877)) (literal (valuationOf q) (882)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 1 3 (meaning867 q) (meaning877 q) (meaning882 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 877 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 877 = false ∨ valuation q 882 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (868)) (literal (valuationOf q) (880)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 2 (meaning868 q) (meaning880 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 880 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (875)) (literal (valuationOf q) (881)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 2 1 (meaning868 q) (meaning875 q) (meaning881 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 875 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 875 = false ∨ valuation q 881 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (876)) (literal (valuationOf q) (882)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 2 2 (meaning868 q) (meaning876 q) (meaning882 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 876 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 876 = false ∨ valuation q 882 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-14, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (881)) (countLit q [-14, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count879 q) 3 (meaning869 q) (meaning881 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 881 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 879 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (879)) (literal (valuationOf q) (889)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 2 1 (meaning857 q) (meaning879 q) (meaning889 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 879 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 879 = false ∨ valuation q 889 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 880 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (880)) (literal (valuationOf q) (890)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 2 2 (meaning857 q) (meaning880 q) (meaning890 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 880 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 880 = false ∨ valuation q 890 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 881 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-1, -3, -4, -5, -8, -11, -12]) + (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12]) (l₂ := [-14, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (881)) (literal (valuationOf q) (891)) (countLit q [-1, -3, -4, -5, -8, -11, -12]) (countLit q [-14, -18, -20, -21, -23, -24, -27, -29]) (count887 q) 2 3 (meaning857 q) (meaning881 q) (meaning891 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 881 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 881 = false ∨ valuation q 891 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E153.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112153
