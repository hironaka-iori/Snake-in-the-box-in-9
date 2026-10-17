import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (890)) (literal (valuationOf q) (898)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 4 (meaning890 q) (meaning898 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 898 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (891)) (literal (valuationOf q) (899)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 5 (meaning891 q) (meaning899 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 899 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (864)) (literal (valuationOf q) (895)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 (meaning864 q) (meaning895 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 895 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 887 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (887)) (literal (valuationOf q) (896)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 1 (meaning864 q) (meaning887 q) (meaning896 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 887 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 887 = false ∨ valuation q 896 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (888)) (literal (valuationOf q) (897)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 2 (meaning864 q) (meaning888 q) (meaning897 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 888 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 888 = false ∨ valuation q 897 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (889)) (literal (valuationOf q) (898)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 3 (meaning864 q) (meaning889 q) (meaning898 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 889 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 889 = false ∨ valuation q 898 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (890)) (literal (valuationOf q) (899)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 4 (meaning864 q) (meaning890 q) (meaning899 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 890 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 890 = false ∨ valuation q 899 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (891)) (literal (valuationOf q) (900)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 1 5 (meaning864 q) (meaning891 q) (meaning900 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 891 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 891 = false ∨ valuation q 900 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (896)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 (meaning865 q) (meaning896 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 896 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (887)) (literal (valuationOf q) (897)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 1 (meaning865 q) (meaning887 q) (meaning897 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 887 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 887 = false ∨ valuation q 897 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (888)) (literal (valuationOf q) (898)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 2 (meaning865 q) (meaning888 q) (meaning898 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 888 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 888 = false ∨ valuation q 898 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (889)) (literal (valuationOf q) (899)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 3 (meaning865 q) (meaning889 q) (meaning899 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 889 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 889 = false ∨ valuation q 899 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (890)) (literal (valuationOf q) (900)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 4 (meaning865 q) (meaning890 q) (meaning900 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 890 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 890 = false ∨ valuation q 900 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (891)) (literal (valuationOf q) (901)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 2 5 (meaning865 q) (meaning891 q) (meaning901 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 891 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 891 = false ∨ valuation q 901 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (897)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 3 (meaning866 q) (meaning897 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 897 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (887)) (literal (valuationOf q) (898)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 3 1 (meaning866 q) (meaning887 q) (meaning898 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 887 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 887 = false ∨ valuation q 898 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (888)) (literal (valuationOf q) (899)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 3 2 (meaning866 q) (meaning888 q) (meaning899 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 888 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 888 = false ∨ valuation q 899 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (889)) (literal (valuationOf q) (900)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 3 3 (meaning866 q) (meaning889 q) (meaning900 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 889 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 889 = false ∨ valuation q 900 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (866)) (literal (valuationOf q) (890)) (literal (valuationOf q) (901)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 3 4 (meaning866 q) (meaning890 q) (meaning901 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 890 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 890 = false ∨ valuation q 901 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (898)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 4 (meaning867 q) (meaning898 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 898 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (887)) (literal (valuationOf q) (899)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 4 1 (meaning867 q) (meaning887 q) (meaning899 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 887 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 887 = false ∨ valuation q 899 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (888)) (literal (valuationOf q) (900)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 4 2 (meaning867 q) (meaning888 q) (meaning900 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 888 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 888 = false ∨ valuation q 900 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (889)) (literal (valuationOf q) (901)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 4 3 (meaning867 q) (meaning889 q) (meaning901 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 889 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 889 = false ∨ valuation q 901 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (890)) (literal (valuationOf q) (902)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 4 4 (meaning867 q) (meaning890 q) (meaning902 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 890 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 890 = false ∨ valuation q 902 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 899 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (868)) (literal (valuationOf q) (899)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 5 (meaning868 q) (meaning899 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 899 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (887)) (literal (valuationOf q) (900)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 5 1 (meaning868 q) (meaning887 q) (meaning900 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 887 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 887 = false ∨ valuation q 900 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (888)) (literal (valuationOf q) (901)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 5 2 (meaning868 q) (meaning888 q) (meaning901 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 888 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 888 = false ∨ valuation q 901 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (889)) (literal (valuationOf q) (902)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 5 3 (meaning868 q) (meaning889 q) (meaning902 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 889 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 889 = false ∨ valuation q 902 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 890 = false ∨ valuationOf q 903 = true := by
  have hs : count895 q = (countLit q [-28, -30, -32, -33, -38, -39, -40]) + (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32, -33, -38, -39, -40]) (l₂ := [-43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (890)) (literal (valuationOf q) (903)) (countLit q [-28, -30, -32, -33, -38, -39, -40]) (countLit q [-43, -46, -48, -50, -52, -55, -56, -59]) (count895 q) 5 4 (meaning868 q) (meaning890 q) (meaning903 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 890 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 890 = false ∨ valuation q 903 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 899 = false ∨ valuationOf q 915 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (899)) (literal (valuationOf q) (915)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 1 5 (meaning837 q) (meaning899 q) (meaning915 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 899 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 899 = false ∨ valuation q 915 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 903 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (903)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 1 9 (meaning837 q) (meaning903 q) (meaning919 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 903 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 903 = false ∨ valuation q 919 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 898 = false ∨ valuationOf q 915 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (898)) (literal (valuationOf q) (915)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 2 4 (meaning838 q) (meaning898 q) (meaning915 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 898 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 898 = false ∨ valuation q 915 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E115.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112115
