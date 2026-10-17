import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 912 = true := by
  have hs : count912 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (912)) (countLit q [-46]) (countLit q [-47]) (count912 q) 1 (meaningNeg47 q) (meaning912 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 912 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 912 = true := by
  have hs : count912 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (912)) (countLit q [-46]) (countLit q [-47]) (count912 q) 1 (meaningNeg46 q) (meaning912 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 912 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 913 = true := by
  have hs : count912 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (913)) (countLit q [-46]) (countLit q [-47]) (count912 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning913 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 913 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 914 = true := by
  have hs : count914 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (914)) (countLit q [-50]) (countLit q [-53]) (count914 q) 1 (meaningNeg53 q) (meaning914 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 914 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 914 = true := by
  have hs : count914 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (914)) (countLit q [-50]) (countLit q [-53]) (count914 q) 1 (meaningNeg50 q) (meaning914 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 914 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 53 = true ∨ valuationOf q 915 = true := by
  have hs : count914 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (915)) (countLit q [-50]) (countLit q [-53]) (count914 q) 1 1 (meaningNeg50 q) (meaningNeg53 q) (meaning915 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 915 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 916 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_right (literal (valuationOf q) (914)) (literal (valuationOf q) (916)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 1 (meaning914 q) (meaning916 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 916 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 917 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_right (literal (valuationOf q) (915)) (literal (valuationOf q) (917)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 2 (meaning915 q) (meaning917 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 917 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 916 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_left (literal (valuationOf q) (912)) (literal (valuationOf q) (916)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 1 (meaning912 q) (meaning916 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 916 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 914 = false ∨ valuationOf q 917 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (914)) (literal (valuationOf q) (917)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 1 1 (meaning912 q) (meaning914 q) (meaning917 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 914 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 914 = false ∨ valuation q 917 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 912 = false ∨ valuationOf q 915 = false ∨ valuationOf q 918 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (912)) (literal (valuationOf q) (915)) (literal (valuationOf q) (918)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 1 2 (meaning912 q) (meaning915 q) (meaning918 q) hs
  change valuationOf q 912 = false ∨ valuationOf q 915 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 912 = false ∨ valuation q 915 = false ∨ valuation q 918 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 917 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_left (literal (valuationOf q) (913)) (literal (valuationOf q) (917)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 2 (meaning913 q) (meaning917 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 917 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 917 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 914 = false ∨ valuationOf q 918 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (914)) (literal (valuationOf q) (918)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 2 1 (meaning913 q) (meaning914 q) (meaning918 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 914 = false ∨ valuationOf q 918 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 914 = false ∨ valuation q 918 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 915 = false ∨ valuationOf q 919 = true := by
  have hs : count916 q = (countLit q [-46, -47]) + (countLit q [-50, -53]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -53])
  have hm := merge_two (literal (valuationOf q) (913)) (literal (valuationOf q) (915)) (literal (valuationOf q) (919)) (countLit q [-46, -47]) (countLit q [-50, -53]) (count916 q) 2 2 (meaning913 q) (meaning915 q) (meaning919 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 915 = false ∨ valuationOf q 919 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 915 = false ∨ valuation q 919 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 920 = true := by
  have hs : count920 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (920)) (countLit q [-54]) (countLit q [-55]) (count920 q) 1 (meaningNeg55 q) (meaning920 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 920 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 920 = true := by
  have hs : count920 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (920)) (countLit q [-54]) (countLit q [-55]) (count920 q) 1 (meaningNeg54 q) (meaning920 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 920 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 920 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 55 = true ∨ valuationOf q 921 = true := by
  have hs : count920 q = (countLit q [-54]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (921)) (countLit q [-54]) (countLit q [-55]) (count920 q) 1 1 (meaningNeg54 q) (meaningNeg55 q) (meaning921 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 921 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 922 = true := by
  have hs : count922 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (922)) (countLit q [-57]) (countLit q [-59]) (count922 q) 1 (meaningNeg59 q) (meaning922 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 922 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 922 = true := by
  have hs : count922 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (922)) (countLit q [-57]) (countLit q [-59]) (count922 q) 1 (meaningNeg57 q) (meaning922 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 922 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 59 = true ∨ valuationOf q 923 = true := by
  have hs : count922 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (923)) (countLit q [-57]) (countLit q [-59]) (count922 q) 1 1 (meaningNeg57 q) (meaningNeg59 q) (meaning923 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 59 = true ∨ valuation q 923 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 924 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_right (literal (valuationOf q) (922)) (literal (valuationOf q) (924)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 1 (meaning922 q) (meaning924 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 924 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 925 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_right (literal (valuationOf q) (923)) (literal (valuationOf q) (925)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 2 (meaning923 q) (meaning925 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 925 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 924 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_left (literal (valuationOf q) (920)) (literal (valuationOf q) (924)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 1 (meaning920 q) (meaning924 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 924 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 922 = false ∨ valuationOf q 925 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (922)) (literal (valuationOf q) (925)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 1 1 (meaning920 q) (meaning922 q) (meaning925 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 922 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 922 = false ∨ valuation q 925 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 923 = false ∨ valuationOf q 926 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (923)) (literal (valuationOf q) (926)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 1 2 (meaning920 q) (meaning923 q) (meaning926 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 923 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 923 = false ∨ valuation q 926 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 925 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_left (literal (valuationOf q) (921)) (literal (valuationOf q) (925)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 2 (meaning921 q) (meaning925 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 925 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 925 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 922 = false ∨ valuationOf q 926 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (922)) (literal (valuationOf q) (926)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 2 1 (meaning921 q) (meaning922 q) (meaning926 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 922 = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 922 = false ∨ valuation q 926 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 923 = false ∨ valuationOf q 927 = true := by
  have hs : count924 q = (countLit q [-54, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-54, -55]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (923)) (literal (valuationOf q) (927)) (countLit q [-54, -55]) (countLit q [-57, -59]) (count924 q) 2 2 (meaning921 q) (meaning923 q) (meaning927 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 923 = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 923 = false ∨ valuation q 927 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_right (literal (valuationOf q) (924)) (literal (valuationOf q) (928)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 1 (meaning924 q) (meaning928 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 928 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 929 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_right (literal (valuationOf q) (925)) (literal (valuationOf q) (929)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 2 (meaning925 q) (meaning929 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 929 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 929 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 930 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_right (literal (valuationOf q) (926)) (literal (valuationOf q) (930)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 3 (meaning926 q) (meaning930 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 930 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 916 = false ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-46, -47, -50, -53]) + (countLit q [-54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -53]) (l₂ := [-54, -55, -57, -59])
  have hm := merge_left (literal (valuationOf q) (916)) (literal (valuationOf q) (928)) (countLit q [-46, -47, -50, -53]) (countLit q [-54, -55, -57, -59]) (count928 q) 1 (meaning916 q) (meaning928 q) hs
  change valuationOf q 916 = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 916 = false ∨ valuation q 928 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E097.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112097
