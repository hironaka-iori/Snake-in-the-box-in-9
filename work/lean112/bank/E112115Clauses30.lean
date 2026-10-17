import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 897 = false ∨ valuationOf q 915 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (897)) (literal (valuationOf q) (915)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 3 3 (meaning839 q) (meaning897 q) (meaning915 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 897 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 897 = false ∨ valuation q 915 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 898 = false ∨ valuationOf q 916 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (898)) (literal (valuationOf q) (916)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 3 4 (meaning839 q) (meaning898 q) (meaning916 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 898 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 898 = false ∨ valuation q 916 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (899)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 3 5 (meaning839 q) (meaning899 q) (meaning917 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 899 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 899 = false ∨ valuation q 917 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (900)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 3 6 (meaning839 q) (meaning900 q) (meaning918 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 900 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 900 = false ∨ valuation q 918 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (901)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 3 7 (meaning839 q) (meaning901 q) (meaning919 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 901 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 901 = false ∨ valuation q 919 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (902)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 3 8 (meaning839 q) (meaning902 q) (meaning920 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 902 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 902 = false ∨ valuation q 920 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 896 = false ∨ valuationOf q 915 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (896)) (literal (valuationOf q) (915)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 2 (meaning840 q) (meaning896 q) (meaning915 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 896 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 896 = false ∨ valuation q 915 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 897 = false ∨ valuationOf q 916 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (897)) (literal (valuationOf q) (916)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 3 (meaning840 q) (meaning897 q) (meaning916 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 897 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 897 = false ∨ valuation q 916 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (898)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 4 (meaning840 q) (meaning898 q) (meaning917 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 898 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 898 = false ∨ valuation q 917 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (899)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 5 (meaning840 q) (meaning899 q) (meaning918 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 899 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 899 = false ∨ valuation q 918 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (900)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 6 (meaning840 q) (meaning900 q) (meaning919 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 900 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 900 = false ∨ valuation q 919 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (901)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 7 (meaning840 q) (meaning901 q) (meaning920 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 901 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 901 = false ∨ valuation q 920 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (840)) (literal (valuationOf q) (902)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 4 8 (meaning840 q) (meaning902 q) (meaning921 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 902 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 902 = false ∨ valuation q 921 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 895 = false ∨ valuationOf q 915 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (895)) (literal (valuationOf q) (915)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 1 (meaning841 q) (meaning895 q) (meaning915 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 895 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 895 = false ∨ valuation q 915 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 896 = false ∨ valuationOf q 916 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (896)) (literal (valuationOf q) (916)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 2 (meaning841 q) (meaning896 q) (meaning916 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 896 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 896 = false ∨ valuation q 916 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 897 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (897)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 3 (meaning841 q) (meaning897 q) (meaning917 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 897 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 897 = false ∨ valuation q 917 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (898)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 4 (meaning841 q) (meaning898 q) (meaning918 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 898 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 898 = false ∨ valuation q 918 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (899)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 5 (meaning841 q) (meaning899 q) (meaning919 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 899 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 899 = false ∨ valuation q 919 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (900)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 6 (meaning841 q) (meaning900 q) (meaning920 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 900 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 900 = false ∨ valuation q 920 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (901)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 7 (meaning841 q) (meaning901 q) (meaning921 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 901 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 901 = false ∨ valuation q 921 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (841)) (literal (valuationOf q) (902)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 5 8 (meaning841 q) (meaning902 q) (meaning922 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 902 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 902 = false ∨ valuation q 922 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 915 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (842)) (literal (valuationOf q) (915)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 (meaning842 q) (meaning915 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 915 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 895 = false ∨ valuationOf q 916 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (895)) (literal (valuationOf q) (916)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 1 (meaning842 q) (meaning895 q) (meaning916 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 895 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 895 = false ∨ valuation q 916 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 896 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (896)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 2 (meaning842 q) (meaning896 q) (meaning917 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 896 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 896 = false ∨ valuation q 917 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 897 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (897)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 3 (meaning842 q) (meaning897 q) (meaning918 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 897 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 897 = false ∨ valuation q 918 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 898 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (898)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 4 (meaning842 q) (meaning898 q) (meaning919 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 898 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 898 = false ∨ valuation q 919 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 899 = false ∨ valuationOf q 920 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (899)) (literal (valuationOf q) (920)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 5 (meaning842 q) (meaning899 q) (meaning920 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 899 = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 899 = false ∨ valuation q 920 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 900 = false ∨ valuationOf q 921 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (900)) (literal (valuationOf q) (921)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 6 (meaning842 q) (meaning900 q) (meaning921 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 900 = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 900 = false ∨ valuation q 921 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (901)) (literal (valuationOf q) (922)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 6 7 (meaning842 q) (meaning901 q) (meaning922 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 901 = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 901 = false ∨ valuation q 922 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 895 = false ∨ valuationOf q 917 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (895)) (literal (valuationOf q) (917)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 7 1 (meaning843 q) (meaning895 q) (meaning917 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 895 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 895 = false ∨ valuation q 917 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 896 = false ∨ valuationOf q 918 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (896)) (literal (valuationOf q) (918)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 7 2 (meaning843 q) (meaning896 q) (meaning918 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 896 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 896 = false ∨ valuation q 918 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 897 = false ∨ valuationOf q 919 = true := by
  have hs : count910 q = (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) + (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (l₂ := [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (897)) (literal (valuationOf q) (919)) (countLit q [-1, -4, -7, -9, -11, -13, -14, -16, -18, -19, -21, -22, -24, -25]) (countLit q [-28, -30, -32, -33, -38, -39, -40, -43, -46, -48, -50, -52, -55, -56, -59]) (count910 q) 7 3 (meaning843 q) (meaning897 q) (meaning919 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 897 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 897 = false ∨ valuation q 919 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E115.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112115
