import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 886 = false ∨ valuationOf q 893 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (877)) (literal (valuationOf q) (886)) (literal (valuationOf q) (893)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 3 4 (meaning877 q) (meaning886 q) (meaning893 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 886 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 886 = false ∨ valuation q 893 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 890 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_left (literal (valuationOf q) (878)) (literal (valuationOf q) (890)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 4 (meaning878 q) (meaning890 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 890 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (883)) (literal (valuationOf q) (891)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 4 1 (meaning878 q) (meaning883 q) (meaning891 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 883 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 883 = false ∨ valuation q 891 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 884 = false ∨ valuationOf q 892 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (884)) (literal (valuationOf q) (892)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 4 2 (meaning878 q) (meaning884 q) (meaning892 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 884 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 884 = false ∨ valuation q 892 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 885 = false ∨ valuationOf q 893 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (885)) (literal (valuationOf q) (893)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 4 3 (meaning878 q) (meaning885 q) (meaning893 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 885 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 885 = false ∨ valuation q 893 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 886 = false ∨ valuationOf q 894 = true := by
  have hs : count887 q = (countLit q [-43, -45, -47, -48]) + (countLit q [-49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -47, -48]) (l₂ := [-49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (878)) (literal (valuationOf q) (886)) (literal (valuationOf q) (894)) (countLit q [-43, -45, -47, -48]) (countLit q [-49, -52, -53, -55]) (count887 q) 4 4 (meaning878 q) (meaning886 q) (meaning894 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 886 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 886 = false ∨ valuation q 894 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (889)) (literal (valuationOf q) (898)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 1 3 (meaning864 q) (meaning889 q) (meaning898 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 889 = false ∨ valuation q 898 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (890)) (literal (valuationOf q) (899)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 1 4 (meaning864 q) (meaning890 q) (meaning899 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 890 = false ∨ valuation q 899 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (891)) (literal (valuationOf q) (900)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 1 5 (meaning864 q) (meaning891 q) (meaning900 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 891 = false ∨ valuation q 900 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 892 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (892)) (literal (valuationOf q) (901)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 1 6 (meaning864 q) (meaning892 q) (meaning901 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 892 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 892 = false ∨ valuation q 901 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 893 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (893)) (literal (valuationOf q) (902)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 1 7 (meaning864 q) (meaning893 q) (meaning902 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 893 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 893 = false ∨ valuation q 902 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 894 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (894)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 1 8 (meaning864 q) (meaning894 q) (meaning903 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 894 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 894 = false ∨ valuation q 903 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (889)) (literal (valuationOf q) (899)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 2 3 (meaning865 q) (meaning889 q) (meaning899 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 889 = false ∨ valuation q 899 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (890)) (literal (valuationOf q) (900)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 2 4 (meaning865 q) (meaning890 q) (meaning900 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 890 = false ∨ valuation q 900 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (891)) (literal (valuationOf q) (901)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 2 5 (meaning865 q) (meaning891 q) (meaning901 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 891 = false ∨ valuation q 901 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (892)) (literal (valuationOf q) (902)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 2 6 (meaning865 q) (meaning892 q) (meaning902 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 892 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 892 = false ∨ valuation q 902 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (893)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 2 7 (meaning865 q) (meaning893 q) (meaning903 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 893 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 893 = false ∨ valuation q 903 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 894 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (894)) (literal (valuationOf q) (904)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 2 8 (meaning865 q) (meaning894 q) (meaning904 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 894 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 894 = false ∨ valuation q 904 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 3 3 (meaning866 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (890)) (literal (valuationOf q) (901)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 3 4 (meaning866 q) (meaning890 q) (meaning901 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 890 = false ∨ valuation q 901 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 891 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (891)) (literal (valuationOf q) (902)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 3 5 (meaning866 q) (meaning891 q) (meaning902 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 891 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 891 = false ∨ valuation q 902 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 892 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (892)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 3 6 (meaning866 q) (meaning892 q) (meaning903 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 892 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 892 = false ∨ valuation q 903 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (893)) (literal (valuationOf q) (904)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 3 7 (meaning866 q) (meaning893 q) (meaning904 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 893 = false ∨ valuation q 904 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 894 = false ∨ valuationOf q 905 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (894)) (literal (valuationOf q) (905)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 3 8 (meaning866 q) (meaning894 q) (meaning905 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 894 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 894 = false ∨ valuation q 905 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (888)) (literal (valuationOf q) (900)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 4 2 (meaning867 q) (meaning888 q) (meaning900 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 888 = false ∨ valuation q 900 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (889)) (literal (valuationOf q) (901)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 4 3 (meaning867 q) (meaning889 q) (meaning901 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 889 = false ∨ valuation q 901 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (890)) (literal (valuationOf q) (902)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 4 4 (meaning867 q) (meaning890 q) (meaning902 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 890 = false ∨ valuation q 902 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 891 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (891)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 4 5 (meaning867 q) (meaning891 q) (meaning903 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 891 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 891 = false ∨ valuation q 903 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (892)) (literal (valuationOf q) (904)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 4 6 (meaning867 q) (meaning892 q) (meaning904 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 892 = false ∨ valuation q 904 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (888)) (literal (valuationOf q) (901)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 5 2 (meaning868 q) (meaning888 q) (meaning901 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 888 = false ∨ valuation q 901 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 890 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (890)) (literal (valuationOf q) (903)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 5 4 (meaning868 q) (meaning890 q) (meaning903 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 890 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 890 = false ∨ valuation q 903 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 891 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-30, -33, -34, -35, -37, -41, -42]) + (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -34, -35, -37, -41, -42]) (l₂ := [-43, -45, -47, -48, -49, -52, -53, -55])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (891)) (literal (valuationOf q) (904)) (countLit q [-30, -33, -34, -35, -37, -41, -42]) (countLit q [-43, -45, -47, -48, -49, -52, -53, -55]) (count895 q) 5 5 (meaning868 q) (meaning891 q) (meaning904 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 891 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 891 = false ∨ valuation q 904 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E081.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112081
