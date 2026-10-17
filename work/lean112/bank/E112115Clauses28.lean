import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (879)) (countLit q [-52]) (countLit q [-55]) (count879 q) 1 (meaningNeg52 q) (meaning879 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 879 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 55 = true ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (880)) (countLit q [-52]) (countLit q [-55]) (count879 q) 1 1 (meaningNeg52 q) (meaningNeg55 q) (meaning880 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 880 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (881)) (countLit q [-56]) (countLit q [-59]) (count881 q) 1 (meaningNeg59 q) (meaning881 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 881 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (881)) (countLit q [-56]) (countLit q [-59]) (count881 q) 1 (meaningNeg56 q) (meaning881 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 881 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 59 = true ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (882)) (countLit q [-56]) (countLit q [-59]) (count881 q) 1 1 (meaningNeg56 q) (meaningNeg59 q) (meaning882 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 882 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (883)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 1 (meaning881 q) (meaning883 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 883 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (884)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 2 (meaning882 q) (meaning884 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 884 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_left (literal (valuationOf q) (879)) (literal (valuationOf q) (883)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 1 (meaning879 q) (meaning883 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 883 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 881 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (881)) (literal (valuationOf q) (884)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 1 1 (meaning879 q) (meaning881 q) (meaning884 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 881 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 881 = false ∨ valuation q 884 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 882 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (882)) (literal (valuationOf q) (885)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 1 2 (meaning879 q) (meaning882 q) (meaning885 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 882 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 882 = false ∨ valuation q 885 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_left (literal (valuationOf q) (880)) (literal (valuationOf q) (884)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 2 (meaning880 q) (meaning884 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 884 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 881 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (881)) (literal (valuationOf q) (885)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 2 1 (meaning880 q) (meaning881 q) (meaning885 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 881 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 881 = false ∨ valuation q 885 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 882 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-52, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (882)) (literal (valuationOf q) (886)) (countLit q [-52, -55]) (countLit q [-56, -59]) (count883 q) 2 2 (meaning880 q) (meaning882 q) (meaning886 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 882 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 882 = false ∨ valuation q 886 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (883)) (literal (valuationOf q) (887)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 1 (meaning883 q) (meaning887 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 887 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (884)) (literal (valuationOf q) (888)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 2 (meaning884 q) (meaning888 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 888 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (885)) (literal (valuationOf q) (889)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 3 (meaning885 q) (meaning889 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 889 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 886 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (886)) (literal (valuationOf q) (890)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 4 (meaning886 q) (meaning890 q) hs
  change valuationOf q 886 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 886 = false ∨ valuation q 890 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (875)) (literal (valuationOf q) (887)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 1 (meaning875 q) (meaning887 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 887 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (883)) (literal (valuationOf q) (888)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 1 1 (meaning875 q) (meaning883 q) (meaning888 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 883 = false ∨ valuation q 888 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (884)) (literal (valuationOf q) (889)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 1 2 (meaning875 q) (meaning884 q) (meaning889 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 884 = false ∨ valuation q 889 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 885 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (885)) (literal (valuationOf q) (890)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 1 3 (meaning875 q) (meaning885 q) (meaning890 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 885 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 885 = false ∨ valuation q 890 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 886 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (886)) (literal (valuationOf q) (891)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 1 4 (meaning875 q) (meaning886 q) (meaning891 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 886 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 886 = false ∨ valuation q 891 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (876)) (literal (valuationOf q) (888)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 2 (meaning876 q) (meaning888 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 888 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (literal (valuationOf q) (889)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 2 1 (meaning876 q) (meaning883 q) (meaning889 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 883 = false ∨ valuation q 889 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (884)) (literal (valuationOf q) (890)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 2 2 (meaning876 q) (meaning884 q) (meaning890 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 884 = false ∨ valuation q 890 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 885 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (885)) (literal (valuationOf q) (891)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 2 3 (meaning876 q) (meaning885 q) (meaning891 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 885 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 885 = false ∨ valuation q 891 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (877)) (literal (valuationOf q) (889)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 3 (meaning877 q) (meaning889 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 889 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (883)) (literal (valuationOf q) (890)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 3 1 (meaning877 q) (meaning883 q) (meaning890 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 883 = false ∨ valuation q 890 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-43, -46, -48, -50]) + (countLit q [-52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -46, -48, -50]) (l₂ := [-52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (884)) (literal (valuationOf q) (891)) (countLit q [-43, -46, -48, -50]) (countLit q [-52, -55, -56, -59]) (count887 q) 3 2 (meaning877 q) (meaning884 q) (meaning891 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 884 = false ∨ valuation q 891 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (887)) (literal (valuationOf q) (895)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 (meaning887 q) (meaning895 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 895 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 888 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (888)) (literal (valuationOf q) (896)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 (meaning888 q) (meaning896 q) hs
  change valuationOf q 888 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 888 = false ∨ valuation q 896 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (897)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 3 (meaning889 q) (meaning897 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 897 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E115.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112115
