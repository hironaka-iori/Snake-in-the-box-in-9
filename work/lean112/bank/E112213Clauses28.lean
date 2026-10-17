import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 886 = false ∨ valuationOf q 893 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (886)) (literal (valuationOf q) (893)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 3 4 (meaning877 q) (meaning886 q) (meaning893 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 886 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 886 = false ∨ valuation q 893 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (883)) (literal (valuationOf q) (891)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 4 1 (meaning878 q) (meaning883 q) (meaning891 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 883 = false ∨ valuation q 891 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 885 = false ∨ valuationOf q 893 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (885)) (literal (valuationOf q) (893)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 4 3 (meaning878 q) (meaning885 q) (meaning893 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 885 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 885 = false ∨ valuation q 893 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (890)) (literal (valuationOf q) (898)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 (meaning890 q) (meaning898 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 898 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (891)) (literal (valuationOf q) (899)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 (meaning891 q) (meaning899 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 899 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (888)) (literal (valuationOf q) (897)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 1 2 (meaning864 q) (meaning888 q) (meaning897 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 888 = false ∨ valuation q 897 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (889)) (literal (valuationOf q) (898)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 1 3 (meaning864 q) (meaning889 q) (meaning898 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 889 = false ∨ valuation q 898 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (890)) (literal (valuationOf q) (899)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 1 4 (meaning864 q) (meaning890 q) (meaning899 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 890 = false ∨ valuation q 899 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (891)) (literal (valuationOf q) (900)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 1 5 (meaning864 q) (meaning891 q) (meaning900 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 891 = false ∨ valuation q 900 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 893 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (893)) (literal (valuationOf q) (902)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 1 7 (meaning864 q) (meaning893 q) (meaning902 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 893 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 893 = false ∨ valuation q 902 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (896)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 (meaning865 q) (meaning896 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 896 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (887)) (literal (valuationOf q) (897)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 1 (meaning865 q) (meaning887 q) (meaning897 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 887 = false ∨ valuation q 897 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (888)) (literal (valuationOf q) (898)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 2 (meaning865 q) (meaning888 q) (meaning898 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 888 = false ∨ valuation q 898 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (889)) (literal (valuationOf q) (899)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 3 (meaning865 q) (meaning889 q) (meaning899 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 889 = false ∨ valuation q 899 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (890)) (literal (valuationOf q) (900)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 4 (meaning865 q) (meaning890 q) (meaning900 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 890 = false ∨ valuation q 900 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (891)) (literal (valuationOf q) (901)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 5 (meaning865 q) (meaning891 q) (meaning901 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 891 = false ∨ valuation q 901 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (892)) (literal (valuationOf q) (902)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 6 (meaning865 q) (meaning892 q) (meaning902 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 892 = false ∨ valuation q 902 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (893)) (literal (valuationOf q) (903)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 2 7 (meaning865 q) (meaning893 q) (meaning903 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 893 = false ∨ valuation q 903 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (897)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 (meaning866 q) (meaning897 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 897 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (887)) (literal (valuationOf q) (898)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 1 (meaning866 q) (meaning887 q) (meaning898 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 887 = false ∨ valuation q 898 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (888)) (literal (valuationOf q) (899)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 2 (meaning866 q) (meaning888 q) (meaning899 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 888 = false ∨ valuation q 899 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 3 (meaning866 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (890)) (literal (valuationOf q) (901)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 4 (meaning866 q) (meaning890 q) (meaning901 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 890 = false ∨ valuation q 901 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 891 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (891)) (literal (valuationOf q) (902)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 5 (meaning866 q) (meaning891 q) (meaning902 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 891 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 891 = false ∨ valuation q 902 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (893)) (literal (valuationOf q) (904)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 3 7 (meaning866 q) (meaning893 q) (meaning904 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 893 = false ∨ valuation q 904 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (898)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 (meaning867 q) (meaning898 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 898 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (887)) (literal (valuationOf q) (899)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 1 (meaning867 q) (meaning887 q) (meaning899 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 887 = false ∨ valuation q 899 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (888)) (literal (valuationOf q) (900)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 2 (meaning867 q) (meaning888 q) (meaning900 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 888 = false ∨ valuation q 900 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (889)) (literal (valuationOf q) (901)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 3 (meaning867 q) (meaning889 q) (meaning901 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 889 = false ∨ valuation q 901 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (890)) (literal (valuationOf q) (902)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 4 (meaning867 q) (meaning890 q) (meaning902 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 890 = false ∨ valuation q 902 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 891 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (891)) (literal (valuationOf q) (903)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 5 (meaning867 q) (meaning891 q) (meaning903 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 891 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 891 = false ∨ valuation q 903 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (892)) (literal (valuationOf q) (904)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 6 (meaning867 q) (meaning892 q) (meaning904 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 892 = false ∨ valuation q 904 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E213.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112213
