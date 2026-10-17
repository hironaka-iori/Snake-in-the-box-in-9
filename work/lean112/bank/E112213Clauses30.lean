import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (902)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 8 (meaning841 q) (meaning902 q) (meaning922 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 902 = false ∨ valuation q 922 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 903 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (903)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 9 (meaning841 q) (meaning903 q) (meaning923 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 903 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 903 = false ∨ valuation q 923 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 904 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (904)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 10 (meaning841 q) (meaning904 q) (meaning924 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 904 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 904 = false ∨ valuation q 924 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 897 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (897)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 3 (meaning842 q) (meaning897 q) (meaning918 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 897 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 897 = false ∨ valuation q 918 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 898 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (898)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 4 (meaning842 q) (meaning898 q) (meaning919 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 898 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 898 = false ∨ valuation q 919 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 899 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (899)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 5 (meaning842 q) (meaning899 q) (meaning920 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 899 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 899 = false ∨ valuation q 920 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 900 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (900)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 6 (meaning842 q) (meaning900 q) (meaning921 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 900 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 900 = false ∨ valuation q 921 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (901)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 7 (meaning842 q) (meaning901 q) (meaning922 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 901 = false ∨ valuation q 922 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 902 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (902)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 8 (meaning842 q) (meaning902 q) (meaning923 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 902 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 902 = false ∨ valuation q 923 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 903 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (903)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 6 9 (meaning842 q) (meaning903 q) (meaning924 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 903 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 903 = false ∨ valuation q 924 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 897 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (897)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 7 3 (meaning843 q) (meaning897 q) (meaning919 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 897 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 897 = false ∨ valuation q 919 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 898 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (898)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 7 4 (meaning843 q) (meaning898 q) (meaning920 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 898 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 898 = false ∨ valuation q 920 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 899 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (899)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 7 5 (meaning843 q) (meaning899 q) (meaning921 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 899 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 899 = false ∨ valuation q 921 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 900 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (900)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 7 6 (meaning843 q) (meaning900 q) (meaning922 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 900 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 900 = false ∨ valuation q 922 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 901 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (901)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 7 7 (meaning843 q) (meaning901 q) (meaning923 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 901 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 901 = false ∨ valuation q 923 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 902 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (902)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 7 8 (meaning843 q) (meaning902 q) (meaning924 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 902 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 902 = false ∨ valuation q 924 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 896 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (896)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 8 2 (meaning844 q) (meaning896 q) (meaning919 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 896 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 896 = false ∨ valuation q 919 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 897 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (897)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 8 3 (meaning844 q) (meaning897 q) (meaning920 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 897 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 897 = false ∨ valuation q 920 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 898 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (898)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 8 4 (meaning844 q) (meaning898 q) (meaning921 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 898 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 898 = false ∨ valuation q 921 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 899 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (899)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 8 5 (meaning844 q) (meaning899 q) (meaning922 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 899 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 899 = false ∨ valuation q 922 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 900 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (900)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 8 6 (meaning844 q) (meaning900 q) (meaning923 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 900 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 900 = false ∨ valuation q 923 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 901 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (901)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 8 7 (meaning844 q) (meaning901 q) (meaning924 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 901 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 901 = false ∨ valuation q 924 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 898 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (898)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 9 4 (meaning845 q) (meaning898 q) (meaning922 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 898 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 898 = false ∨ valuation q 922 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 899 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (899)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 9 5 (meaning845 q) (meaning899 q) (meaning923 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 899 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 899 = false ∨ valuation q 923 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (929)) (countLit q [-62]) (countLit q [-64]) (count929 q) 1 (meaningNeg64 q) (meaning929 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 929 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (929)) (countLit q [-62]) (countLit q [-64]) (count929 q) 1 (meaningNeg62 q) (meaning929 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 929 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 64 = true ∨ valuationOf q 930 = true := by
  have hs : count929 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (930)) (countLit q [-62]) (countLit q [-64]) (count929 q) 1 1 (meaningNeg62 q) (meaningNeg64 q) (meaning930 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 930 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-59]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (929)) (literal (valuationOf q) (931)) (countLit q [-59]) (countLit q [-62, -64]) (count931 q) 1 (meaning929 q) (meaning931 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 931 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-59]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (932)) (countLit q [-59]) (countLit q [-62, -64]) (count931 q) 2 (meaning930 q) (meaning932 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 932 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-59]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -64])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (931)) (countLit q [-59]) (countLit q [-62, -64]) (count931 q) 1 (meaningNeg59 q) (meaning931 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 931 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-59]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (929)) (literal (valuationOf q) (932)) (countLit q [-59]) (countLit q [-62, -64]) (count931 q) 1 1 (meaningNeg59 q) (meaning929 q) (meaning932 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 929 = false ∨ valuation q 932 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-59]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (930)) (literal (valuationOf q) (933)) (countLit q [-59]) (countLit q [-62, -64]) (count931 q) 1 2 (meaningNeg59 q) (meaning930 q) (meaning933 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 930 = false ∨ valuation q 933 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E213.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112213
