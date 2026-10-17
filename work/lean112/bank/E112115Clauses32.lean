import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (936)) (countLit q [-70]) (countLit q [-73]) (count936 q) 1 (meaningNeg73 q) (meaning936 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 936 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (936)) (countLit q [-70]) (countLit q [-73]) (count936 q) 1 (meaningNeg70 q) (meaning936 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 936 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 73 = true ∨ valuationOf q 937 = true := by
  have hs : count936 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (937)) (countLit q [-70]) (countLit q [-73]) (count936 q) 1 1 (meaningNeg70 q) (meaningNeg73 q) (meaning937 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 73 = true ∨ valuation q 937 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_right (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 1 (meaning936 q) (meaning938 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_right (literal (valuationOf q) (937)) (literal (valuationOf q) (939)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 2 (meaning937 q) (meaning939 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 939 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_left (literal (valuationOf q) (934)) (literal (valuationOf q) (938)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 1 (meaning934 q) (meaning938 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 938 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (936)) (literal (valuationOf q) (939)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 1 1 (meaning934 q) (meaning936 q) (meaning939 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 936 = false ∨ valuation q 939 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (937)) (literal (valuationOf q) (940)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 1 2 (meaning934 q) (meaning937 q) (meaning940 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 937 = false ∨ valuation q 940 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (939)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 2 (meaning935 q) (meaning939 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 939 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 2 1 (meaning935 q) (meaning936 q) (meaning940 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 936 = false ∨ valuation q 940 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 937 = false ∨ valuationOf q 941 = true := by
  have hs : count938 q = (countLit q [-67, -68]) + (countLit q [-70, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-70, -73])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (937)) (literal (valuationOf q) (941)) (countLit q [-67, -68]) (countLit q [-70, -73]) (count938 q) 2 2 (meaning935 q) (meaning937 q) (meaning941 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 937 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 937 = false ∨ valuation q 941 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_right (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 1 (meaning938 q) (meaning942 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 942 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 2 (meaning939 q) (meaning943 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 943 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_right (literal (valuationOf q) (940)) (literal (valuationOf q) (944)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 3 (meaning940 q) (meaning944 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 944 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_left (literal (valuationOf q) (931)) (literal (valuationOf q) (942)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 1 (meaning931 q) (meaning942 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 942 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 938 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (938)) (literal (valuationOf q) (943)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 1 1 (meaning931 q) (meaning938 q) (meaning943 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 938 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 938 = false ∨ valuation q 943 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (939)) (literal (valuationOf q) (944)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 1 2 (meaning931 q) (meaning939 q) (meaning944 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 939 = false ∨ valuation q 944 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (940)) (literal (valuationOf q) (945)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 1 3 (meaning931 q) (meaning940 q) (meaning945 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 940 = false ∨ valuation q 945 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (941)) (literal (valuationOf q) (946)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 1 4 (meaning931 q) (meaning941 q) (meaning946 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 941 = false ∨ valuation q 946 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (943)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 2 (meaning932 q) (meaning943 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 943 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 938 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (938)) (literal (valuationOf q) (944)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 2 1 (meaning932 q) (meaning938 q) (meaning944 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 938 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 938 = false ∨ valuation q 944 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (939)) (literal (valuationOf q) (945)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 2 2 (meaning932 q) (meaning939 q) (meaning945 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 939 = false ∨ valuation q 945 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (940)) (literal (valuationOf q) (946)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 2 3 (meaning932 q) (meaning940 q) (meaning946 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 940 = false ∨ valuation q 946 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_left (literal (valuationOf q) (933)) (literal (valuationOf q) (944)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 3 (meaning933 q) (meaning944 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 944 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 938 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (938)) (literal (valuationOf q) (945)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 3 1 (meaning933 q) (meaning938 q) (meaning945 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 938 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 938 = false ∨ valuation q 945 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 939 = false ∨ valuationOf q 946 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (939)) (literal (valuationOf q) (946)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 3 2 (meaning933 q) (meaning939 q) (meaning946 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 939 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 939 = false ∨ valuation q 946 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true := by
  have hs : count942 q = (countLit q [-61, -62, -65]) + (countLit q [-67, -68, -70, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65]) (l₂ := [-67, -68, -70, -73])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (940)) (literal (valuationOf q) (947)) (countLit q [-61, -62, -65]) (countLit q [-67, -68, -70, -73]) (count942 q) 3 3 (meaning933 q) (meaning940 q) (meaning947 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 940 = false ∨ valuation q 947 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (949)) (countLit q [-74]) (countLit q [-75]) (count949 q) 1 (meaningNeg75 q) (meaning949 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 949 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (949)) (countLit q [-74]) (countLit q [-75]) (count949 q) 1 (meaningNeg74 q) (meaning949 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 949 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 75 = true ∨ valuationOf q 950 = true := by
  have hs : count949 q = (countLit q [-74]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (950)) (countLit q [-74]) (countLit q [-75]) (count949 q) 1 1 (meaningNeg74 q) (meaningNeg75 q) (meaning950 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 75 = true ∨ valuation q 950 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (951)) (countLit q [-78]) (countLit q [-79]) (count951 q) 1 (meaningNeg79 q) (meaning951 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 951 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (951)) (countLit q [-78]) (countLit q [-79]) (count951 q) 1 (meaningNeg78 q) (meaning951 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 951 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E115.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112115
