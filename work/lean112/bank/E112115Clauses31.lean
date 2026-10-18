import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 898 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (898)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 7 4 (meaning843 q) (meaning898 q) (meaning920 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 898 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 898 = false ∨ valuation q 920 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 899 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (899)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 7 5 (meaning843 q) (meaning899 q) (meaning921 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 899 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 899 = false ∨ valuation q 921 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 900 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (900)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 7 6 (meaning843 q) (meaning900 q) (meaning922 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 900 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 900 = false ∨ valuation q 922 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (844)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 (meaning844 q) (meaning917 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 917 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 895 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (895)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 1 (meaning844 q) (meaning895 q) (meaning918 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 895 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 895 = false ∨ valuation q 918 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 896 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (896)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 2 (meaning844 q) (meaning896 q) (meaning919 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 896 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 896 = false ∨ valuation q 919 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 897 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (897)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 3 (meaning844 q) (meaning897 q) (meaning920 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 897 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 897 = false ∨ valuation q 920 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 898 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (898)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 4 (meaning844 q) (meaning898 q) (meaning921 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 898 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 898 = false ∨ valuation q 921 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 899 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (899)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 5 (meaning844 q) (meaning899 q) (meaning922 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 899 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 899 = false ∨ valuation q 922 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 900 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (900)) (literal (valuationOf q) (923)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 8 6 (meaning844 q) (meaning900 q) (meaning923 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 900 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 900 = false ∨ valuation q 923 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (845)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 9 (meaning845 q) (meaning918 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 918 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 895 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (895)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 9 1 (meaning845 q) (meaning895 q) (meaning919 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 895 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 895 = false ∨ valuation q 919 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 896 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (896)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 9 2 (meaning845 q) (meaning896 q) (meaning920 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 896 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 896 = false ∨ valuation q 920 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 897 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (897)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 9 3 (meaning845 q) (meaning897 q) (meaning921 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 897 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 897 = false ∨ valuation q 921 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 898 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (898)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 9 4 (meaning845 q) (meaning898 q) (meaning922 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 898 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 898 = false ∨ valuation q 922 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 895 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (895)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 10 1 (meaning846 q) (meaning895 q) (meaning920 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 895 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 895 = false ∨ valuation q 920 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 896 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (896)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 10 2 (meaning846 q) (meaning896 q) (meaning921 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 896 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 896 = false ∨ valuation q 921 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 897 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (897)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 10 3 (meaning846 q) (meaning897 q) (meaning922 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 897 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 897 = false ∨ valuation q 922 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 898 = false ∨ valuationOf q 923 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (898)) (literal (valuationOf q) (923)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 10 4 (meaning846 q) (meaning898 q) (meaning923 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 898 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 898 = false ∨ valuation q 923 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 895 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (895)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 11 1 (meaning847 q) (meaning895 q) (meaning921 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 895 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 895 = false ∨ valuation q 921 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 896 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (896)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 11 2 (meaning847 q) (meaning896 q) (meaning922 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 896 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 896 = false ∨ valuation q 922 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-62]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (929)) (countLit q [-62]) (countLit q [-65]) (count929 q) 1 (meaningNeg65 q) (meaning929 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 929 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 929 = true := by
  have hs : count929 q = (countLit q [-62]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (929)) (countLit q [-62]) (countLit q [-65]) (count929 q) 1 (meaningNeg62 q) (meaning929 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 929 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 65 = true ∨ valuationOf q 930 = true := by
  have hs : count929 q = (countLit q [-62]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-65)) (literal (valuationOf q) (930)) (countLit q [-62]) (countLit q [-65]) (count929 q) 1 1 (meaningNeg62 q) (meaningNeg65 q) (meaning930 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 65)) = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 65 = true ∨ valuation q 930 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-61]) + (countLit q [-62, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -65])
  have hm := merge_right (literal (valuationOf q) (929)) (literal (valuationOf q) (931)) (countLit q [-61]) (countLit q [-62, -65]) (count931 q) 1 (meaning929 q) (meaning931 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 931 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-61]) + (countLit q [-62, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -65])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (932)) (countLit q [-61]) (countLit q [-62, -65]) (count931 q) 2 (meaning930 q) (meaning932 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 932 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 931 = true := by
  have hs : count931 q = (countLit q [-61]) + (countLit q [-62, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -65])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (931)) (countLit q [-61]) (countLit q [-62, -65]) (count931 q) 1 (meaningNeg61 q) (meaning931 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 931 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true := by
  have hs : count931 q = (countLit q [-61]) + (countLit q [-62, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -65])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (929)) (literal (valuationOf q) (932)) (countLit q [-61]) (countLit q [-62, -65]) (count931 q) 1 1 (meaningNeg61 q) (meaning929 q) (meaning932 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 929 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 929 = false ∨ valuation q 932 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true := by
  have hs : count931 q = (countLit q [-61]) + (countLit q [-62, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -65])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (930)) (literal (valuationOf q) (933)) (countLit q [-61]) (countLit q [-62, -65]) (count931 q) 1 2 (meaningNeg61 q) (meaning930 q) (meaning933 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 930 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 930 = false ∨ valuation q 933 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (934)) (countLit q [-67]) (countLit q [-68]) (count934 q) 1 (meaningNeg68 q) (meaning934 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 934 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (934)) (countLit q [-67]) (countLit q [-68]) (count934 q) 1 (meaningNeg67 q) (meaning934 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 934 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 68 = true ∨ valuationOf q 935 = true := by
  have hs : count934 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (935)) (countLit q [-67]) (countLit q [-68]) (count934 q) 1 1 (meaningNeg67 q) (meaningNeg68 q) (meaning935 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 935 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E115.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112115
