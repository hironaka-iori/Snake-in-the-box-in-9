import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 2 2 (meaning872 q) (meaning874 q) (meaning878 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = false ∨ valuation q 878 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (879)) (countLit q [-51]) (countLit q [-52]) (count879 q) 1 (meaningNeg52 q) (meaning879 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 879 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (879)) (countLit q [-51]) (countLit q [-52]) (count879 q) 1 (meaningNeg51 q) (meaning879 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 879 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (880)) (countLit q [-51]) (countLit q [-52]) (count879 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning880 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 880 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (881)) (countLit q [-55]) (countLit q [-56]) (count881 q) 1 (meaningNeg56 q) (meaning881 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 881 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 881 = true := by
  have hs : count881 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (881)) (countLit q [-55]) (countLit q [-56]) (count881 q) 1 (meaningNeg55 q) (meaning881 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 881 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 56 = true ∨ valuationOf q 882 = true := by
  have hs : count881 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (882)) (countLit q [-55]) (countLit q [-56]) (count881 q) 1 1 (meaningNeg55 q) (meaningNeg56 q) (meaning882 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 882 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (881)) (literal (valuationOf q) (883)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 1 (meaning881 q) (meaning883 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 883 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (884)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 2 (meaning882 q) (meaning884 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 884 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 883 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (879)) (literal (valuationOf q) (883)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 1 (meaning879 q) (meaning883 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 883 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 881 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (881)) (literal (valuationOf q) (884)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 1 1 (meaning879 q) (meaning881 q) (meaning884 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 881 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 881 = false ∨ valuation q 884 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 882 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (882)) (literal (valuationOf q) (885)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 1 2 (meaning879 q) (meaning882 q) (meaning885 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 882 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 882 = false ∨ valuation q 885 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 884 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (880)) (literal (valuationOf q) (884)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 2 (meaning880 q) (meaning884 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 884 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 881 = false ∨ valuationOf q 885 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (881)) (literal (valuationOf q) (885)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 2 1 (meaning880 q) (meaning881 q) (meaning885 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 881 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 881 = false ∨ valuation q 885 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 882 = false ∨ valuationOf q 886 = true := by
  have hs : count883 q = (countLit q [-51, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (882)) (literal (valuationOf q) (886)) (countLit q [-51, -52]) (countLit q [-55, -56]) (count883 q) 2 2 (meaning880 q) (meaning882 q) (meaning886 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 882 = false ∨ valuationOf q 886 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 882 = false ∨ valuation q 886 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (883)) (literal (valuationOf q) (887)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 1 (meaning883 q) (meaning887 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 887 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (884)) (literal (valuationOf q) (888)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 2 (meaning884 q) (meaning888 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 888 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 885 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_right (literal (valuationOf q) (885)) (literal (valuationOf q) (889)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 3 (meaning885 q) (meaning889 q) hs
  change valuationOf q 885 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 885 = false ∨ valuation q 889 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (875)) (literal (valuationOf q) (887)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 1 (meaning875 q) (meaning887 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 887 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (883)) (literal (valuationOf q) (888)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 1 1 (meaning875 q) (meaning883 q) (meaning888 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 883 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 883 = false ∨ valuation q 888 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (884)) (literal (valuationOf q) (889)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 1 2 (meaning875 q) (meaning884 q) (meaning889 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 884 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 884 = false ∨ valuation q 889 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 885 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (885)) (literal (valuationOf q) (890)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 1 3 (meaning875 q) (meaning885 q) (meaning890 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 885 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 885 = false ∨ valuation q 890 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 886 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (875)) (literal (valuationOf q) (886)) (literal (valuationOf q) (891)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 1 4 (meaning875 q) (meaning886 q) (meaning891 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 886 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 886 = false ∨ valuation q 891 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 888 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (876)) (literal (valuationOf q) (888)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 2 (meaning876 q) (meaning888 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 888 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 888 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (883)) (literal (valuationOf q) (889)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 2 1 (meaning876 q) (meaning883 q) (meaning889 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 883 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 883 = false ∨ valuation q 889 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (884)) (literal (valuationOf q) (890)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 2 2 (meaning876 q) (meaning884 q) (meaning890 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 884 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 884 = false ∨ valuation q 890 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 885 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (885)) (literal (valuationOf q) (891)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 2 3 (meaning876 q) (meaning885 q) (meaning891 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 885 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 885 = false ∨ valuation q 891 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 886 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (876)) (literal (valuationOf q) (886)) (literal (valuationOf q) (892)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 2 4 (meaning876 q) (meaning886 q) (meaning892 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 886 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 886 = false ∨ valuation q 892 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 889 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (877)) (literal (valuationOf q) (889)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 3 (meaning877 q) (meaning889 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 889 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (883)) (literal (valuationOf q) (890)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 3 1 (meaning877 q) (meaning883 q) (meaning890 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 883 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 883 = false ∨ valuation q 890 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (884)) (literal (valuationOf q) (891)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 3 2 (meaning877 q) (meaning884 q) (meaning891 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 884 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 884 = false ∨ valuation q 891 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 885 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-42, -44, -46, -49]) + (countLit q [-51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-42, -44, -46, -49]) (l₂ := [-51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (885)) (literal (valuationOf q) (892)) (countLit q [-42, -44, -46, -49]) (countLit q [-51, -52, -55, -56]) (count887 q) 3 3 (meaning877 q) (meaning885 q) (meaning892 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 885 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 885 = false ∨ valuation q 892 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E213.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112213
