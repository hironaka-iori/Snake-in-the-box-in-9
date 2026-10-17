import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 893 = false ∨ valuationOf q 905 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (893)) (literal (valuationOf q) (905)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 4 7 (meaning867 q) (meaning893 q) (meaning905 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 893 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 893 = false ∨ valuation q 905 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (868)) (literal (valuationOf q) (899)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 (meaning868 q) (meaning899 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 899 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (887)) (literal (valuationOf q) (900)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 1 (meaning868 q) (meaning887 q) (meaning900 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 887 = false ∨ valuation q 900 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (888)) (literal (valuationOf q) (901)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 2 (meaning868 q) (meaning888 q) (meaning901 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 888 = false ∨ valuation q 901 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (889)) (literal (valuationOf q) (902)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 3 (meaning868 q) (meaning889 q) (meaning902 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 889 = false ∨ valuation q 902 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 890 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (890)) (literal (valuationOf q) (903)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 4 (meaning868 q) (meaning890 q) (meaning903 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 890 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 890 = false ∨ valuation q 903 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 891 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (891)) (literal (valuationOf q) (904)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 5 (meaning868 q) (meaning891 q) (meaning904 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 891 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 891 = false ∨ valuation q 904 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 892 = false ∨ valuationOf q 905 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (892)) (literal (valuationOf q) (905)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 5 6 (meaning868 q) (meaning892 q) (meaning905 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 892 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 892 = false ∨ valuation q 905 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (900)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 6 (meaning869 q) (meaning900 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 900 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 887 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (887)) (literal (valuationOf q) (901)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 6 1 (meaning869 q) (meaning887 q) (meaning901 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 887 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 887 = false ∨ valuation q 901 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 888 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (888)) (literal (valuationOf q) (902)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 6 2 (meaning869 q) (meaning888 q) (meaning902 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 888 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 888 = false ∨ valuation q 902 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 889 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (889)) (literal (valuationOf q) (903)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 6 3 (meaning869 q) (meaning889 q) (meaning903 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 889 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 889 = false ∨ valuation q 903 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 890 = false ∨ valuationOf q 904 = true := by
  have hs : count895 q = (countLit q [-27, -30, -33, -35, -37, -39, -40]) + (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33, -35, -37, -39, -40]) (l₂ := [-42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (890)) (literal (valuationOf q) (904)) (countLit q [-27, -30, -33, -35, -37, -39, -40]) (countLit q [-42, -44, -46, -49, -51, -52, -55, -56]) (count895 q) 6 4 (meaning869 q) (meaning890 q) (meaning904 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 890 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 890 = false ∨ valuation q 904 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 904 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (904)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 2 10 (meaning838 q) (meaning904 q) (meaning921 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 904 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 904 = false ∨ valuation q 921 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (899)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 3 5 (meaning839 q) (meaning899 q) (meaning917 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 899 = false ∨ valuation q 917 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (900)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 3 6 (meaning839 q) (meaning900 q) (meaning918 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 900 = false ∨ valuation q 918 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (901)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 3 7 (meaning839 q) (meaning901 q) (meaning919 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 901 = false ∨ valuation q 919 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (902)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 3 8 (meaning839 q) (meaning902 q) (meaning920 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 902 = false ∨ valuation q 920 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 903 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (903)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 3 9 (meaning839 q) (meaning903 q) (meaning921 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 903 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 903 = false ∨ valuation q 921 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 904 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (904)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 3 10 (meaning839 q) (meaning904 q) (meaning922 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 904 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 904 = false ∨ valuation q 922 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (898)) (literal (valuationOf q) (917)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 4 (meaning840 q) (meaning898 q) (meaning917 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 898 = false ∨ valuation q 917 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (899)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 5 (meaning840 q) (meaning899 q) (meaning918 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 899 = false ∨ valuation q 918 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (900)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 6 (meaning840 q) (meaning900 q) (meaning919 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 900 = false ∨ valuation q 919 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (901)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 7 (meaning840 q) (meaning901 q) (meaning920 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 901 = false ∨ valuation q 920 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (902)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 8 (meaning840 q) (meaning902 q) (meaning921 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 902 = false ∨ valuation q 921 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (903)) (literal (valuationOf q) (922)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 9 (meaning840 q) (meaning903 q) (meaning922 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 903 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 903 = false ∨ valuation q 922 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (904)) (literal (valuationOf q) (923)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 10 (meaning840 q) (meaning904 q) (meaning923 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 904 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 904 = false ∨ valuation q 923 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (905)) (literal (valuationOf q) (924)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 4 11 (meaning840 q) (meaning905 q) (meaning924 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 905 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 905 = false ∨ valuation q 924 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (898)) (literal (valuationOf q) (918)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 4 (meaning841 q) (meaning898 q) (meaning918 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 898 = false ∨ valuation q 918 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (899)) (literal (valuationOf q) (919)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 5 (meaning841 q) (meaning899 q) (meaning919 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 899 = false ∨ valuation q 919 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (900)) (literal (valuationOf q) (920)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 6 (meaning841 q) (meaning900 q) (meaning920 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 900 = false ∨ valuation q 920 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) + (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (l₂ := [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (901)) (literal (valuationOf q) (921)) (countLit q [-1, -3, -6, -8, -11, -13, -14, -16, -17, -20, -21, -22, -24, -25]) (countLit q [-27, -30, -33, -35, -37, -39, -40, -42, -44, -46, -49, -51, -52, -55, -56]) (count910 q) 5 7 (meaning841 q) (meaning901 q) (meaning921 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 901 = false ∨ valuation q 921 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E213.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112213
