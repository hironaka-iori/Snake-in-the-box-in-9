import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 897 = false ∨ valuationOf q 907 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (897)) (literal (valuationOf q) (907)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 2 7 (meaning869 q) (meaning897 q) (meaning907 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 897 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 897 = false ∨ valuation q 907 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 892 = false ∨ valuationOf q 903 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (892)) (literal (valuationOf q) (903)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 3 2 (meaning870 q) (meaning892 q) (meaning903 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 892 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 892 = false ∨ valuation q 903 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (893)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 3 3 (meaning870 q) (meaning893 q) (meaning904 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 893 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 893 = false ∨ valuation q 904 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 894 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (894)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 3 4 (meaning870 q) (meaning894 q) (meaning905 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 894 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 894 = false ∨ valuation q 905 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 895 = false ∨ valuationOf q 906 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (895)) (literal (valuationOf q) (906)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 3 5 (meaning870 q) (meaning895 q) (meaning906 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 895 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 895 = false ∨ valuation q 906 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 896 = false ∨ valuationOf q 907 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (896)) (literal (valuationOf q) (907)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 3 6 (meaning870 q) (meaning896 q) (meaning907 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 896 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 896 = false ∨ valuation q 907 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 897 = false ∨ valuationOf q 908 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (897)) (literal (valuationOf q) (908)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 3 7 (meaning870 q) (meaning897 q) (meaning908 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 897 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 897 = false ∨ valuation q 908 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (892)) (literal (valuationOf q) (904)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 4 2 (meaning871 q) (meaning892 q) (meaning904 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 892 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 892 = false ∨ valuation q 904 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 893 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (893)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 4 3 (meaning871 q) (meaning893 q) (meaning905 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 893 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 893 = false ∨ valuation q 905 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 894 = false ∨ valuationOf q 906 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (894)) (literal (valuationOf q) (906)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 4 4 (meaning871 q) (meaning894 q) (meaning906 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 894 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 894 = false ∨ valuation q 906 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 895 = false ∨ valuationOf q 907 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (895)) (literal (valuationOf q) (907)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 4 5 (meaning871 q) (meaning895 q) (meaning907 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 895 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 895 = false ∨ valuation q 907 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 896 = false ∨ valuationOf q 908 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (896)) (literal (valuationOf q) (908)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 4 6 (meaning871 q) (meaning896 q) (meaning908 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 896 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 896 = false ∨ valuation q 908 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 892 = false ∨ valuationOf q 905 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (892)) (literal (valuationOf q) (905)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 5 2 (meaning872 q) (meaning892 q) (meaning905 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 892 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 892 = false ∨ valuation q 905 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 893 = false ∨ valuationOf q 906 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (893)) (literal (valuationOf q) (906)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 5 3 (meaning872 q) (meaning893 q) (meaning906 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 893 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 893 = false ∨ valuation q 906 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 894 = false ∨ valuationOf q 907 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (894)) (literal (valuationOf q) (907)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 5 4 (meaning872 q) (meaning894 q) (meaning907 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 894 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 894 = false ∨ valuation q 907 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 895 = false ∨ valuationOf q 908 = true := by
  have hs : count899 q = (countLit q [-27, -29, -30, -32, -36, -37, -39]) + (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -36, -37, -39]) (l₂ := [-41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (895)) (literal (valuationOf q) (908)) (countLit q [-27, -29, -30, -32, -36, -37, -39]) (countLit q [-41, -45, -46, -49, -50, -51, -54, -55]) (count899 q) 5 5 (meaning872 q) (meaning895 q) (meaning908 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 895 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 895 = false ∨ valuation q 908 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 905 = false ∨ valuationOf q 923 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (905)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 3 7 (meaning843 q) (meaning905 q) (meaning923 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 905 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 905 = false ∨ valuation q 923 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 906 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (906)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 3 8 (meaning843 q) (meaning906 q) (meaning924 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 906 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 906 = false ∨ valuation q 924 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 907 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (907)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 3 9 (meaning843 q) (meaning907 q) (meaning925 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 907 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 907 = false ∨ valuation q 925 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 908 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (908)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 3 10 (meaning843 q) (meaning908 q) (meaning926 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 908 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 908 = false ∨ valuation q 926 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (903)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 4 5 (meaning844 q) (meaning903 q) (meaning922 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 903 = false ∨ valuation q 922 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (904)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 4 6 (meaning844 q) (meaning904 q) (meaning923 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 904 = false ∨ valuation q 923 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (905)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 4 7 (meaning844 q) (meaning905 q) (meaning924 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 905 = false ∨ valuation q 924 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 906 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (906)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 4 8 (meaning844 q) (meaning906 q) (meaning925 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 906 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 906 = false ∨ valuation q 925 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 907 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (907)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 4 9 (meaning844 q) (meaning907 q) (meaning926 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 907 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 907 = false ∨ valuation q 926 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 908 = false ∨ valuationOf q 927 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (908)) (literal (valuationOf q) (927)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 4 10 (meaning844 q) (meaning908 q) (meaning927 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 908 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 908 = false ∨ valuation q 927 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (902)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 4 (meaning845 q) (meaning902 q) (meaning922 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 902 = false ∨ valuation q 922 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 903 = false ∨ valuationOf q 923 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (903)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 5 (meaning845 q) (meaning903 q) (meaning923 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 903 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 903 = false ∨ valuation q 923 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 904 = false ∨ valuationOf q 924 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (904)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 6 (meaning845 q) (meaning904 q) (meaning924 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 904 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 904 = false ∨ valuation q 924 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 905 = false ∨ valuationOf q 925 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (905)) (literal (valuationOf q) (925)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 7 (meaning845 q) (meaning905 q) (meaning925 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 905 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 905 = false ∨ valuation q 925 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 906 = false ∨ valuationOf q 926 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (906)) (literal (valuationOf q) (926)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 8 (meaning845 q) (meaning906 q) (meaning926 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 906 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 906 = false ∨ valuation q 926 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 907 = false ∨ valuationOf q 927 = true := by
  have hs : count914 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) + (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (l₂ := [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (907)) (literal (valuationOf q) (927)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24]) (countLit q [-27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (count914 q) 5 9 (meaning845 q) (meaning907 q) (meaning927 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 907 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 907 = false ∨ valuation q 927 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E159.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112159
