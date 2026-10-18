import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (934)) (countLit q [-66]) (countLit q [-69]) (count934 q) 1 (meaningNeg69 q) (meaning934 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 934 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (934)) (countLit q [-66]) (countLit q [-69]) (count934 q) 1 (meaningNeg66 q) (meaning934 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 934 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 69 = true ∨ valuationOf q 935 = true := by
  have hs : count934 q = (countLit q [-66]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (935)) (countLit q [-66]) (countLit q [-69]) (count934 q) 1 1 (meaningNeg66 q) (meaningNeg69 q) (meaning935 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 69 = true ∨ valuation q 935 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (936)) (countLit q [-72]) (countLit q [-73]) (count936 q) 1 (meaningNeg73 q) (meaning936 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 936 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 936 = true := by
  have hs : count936 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (936)) (countLit q [-72]) (countLit q [-73]) (count936 q) 1 (meaningNeg72 q) (meaning936 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 936 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 937 = true := by
  have hs : count936 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (937)) (countLit q [-72]) (countLit q [-73]) (count936 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning937 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 937 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (936)) (literal (valuationOf q) (938)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 1 (meaning936 q) (meaning938 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 938 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (937)) (literal (valuationOf q) (939)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 2 (meaning937 q) (meaning939 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 939 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 938 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (934)) (literal (valuationOf q) (938)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 1 (meaning934 q) (meaning938 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 938 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 938 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (936)) (literal (valuationOf q) (939)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 1 1 (meaning934 q) (meaning936 q) (meaning939 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 936 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 936 = false ∨ valuation q 939 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (937)) (literal (valuationOf q) (940)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 1 2 (meaning934 q) (meaning937 q) (meaning940 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 937 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 937 = false ∨ valuation q 940 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 939 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (939)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 2 (meaning935 q) (meaning939 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 939 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count938 q = (countLit q [-66, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-66, -69]) (countLit q [-72, -73]) (count938 q) 2 1 (meaning935 q) (meaning936 q) (meaning940 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 936 = false ∨ valuation q 940 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 1 (meaning938 q) (meaning942 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 942 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 2 (meaning939 q) (meaning943 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 943 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_right (literal (valuationOf q) (940)) (literal (valuationOf q) (944)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 3 (meaning940 q) (meaning944 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 944 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (931)) (literal (valuationOf q) (942)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 1 (meaning931 q) (meaning942 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 942 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 938 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (938)) (literal (valuationOf q) (943)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 1 1 (meaning931 q) (meaning938 q) (meaning943 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 938 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 938 = false ∨ valuation q 943 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (939)) (literal (valuationOf q) (944)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 1 2 (meaning931 q) (meaning939 q) (meaning944 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 939 = false ∨ valuation q 944 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (940)) (literal (valuationOf q) (945)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 1 3 (meaning931 q) (meaning940 q) (meaning945 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 940 = false ∨ valuation q 945 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (943)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 2 (meaning932 q) (meaning943 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 943 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 938 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (938)) (literal (valuationOf q) (944)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 2 1 (meaning932 q) (meaning938 q) (meaning944 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 938 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 938 = false ∨ valuation q 944 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (939)) (literal (valuationOf q) (945)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 2 2 (meaning932 q) (meaning939 q) (meaning945 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 939 = false ∨ valuation q 945 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-59, -62, -64]) + (countLit q [-66, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -64]) (l₂ := [-66, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (933)) (literal (valuationOf q) (944)) (countLit q [-59, -62, -64]) (countLit q [-66, -69, -72, -73]) (count942 q) 3 (meaning933 q) (meaning944 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 944 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (949)) (countLit q [-74]) (countLit q [-76]) (count949 q) 1 (meaningNeg76 q) (meaning949 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 949 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (949)) (countLit q [-74]) (countLit q [-76]) (count949 q) 1 (meaningNeg74 q) (meaning949 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 949 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 950 = true := by
  have hs : count949 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (950)) (countLit q [-74]) (countLit q [-76]) (count949 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning950 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 950 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (951)) (countLit q [-79]) (countLit q [-81]) (count951 q) 1 (meaningNeg81 q) (meaning951 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 951 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (951)) (countLit q [-79]) (countLit q [-81]) (count951 q) 1 (meaningNeg79 q) (meaning951 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 951 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 81 = true ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (952)) (countLit q [-79]) (countLit q [-81]) (count951 q) 1 1 (meaningNeg79 q) (meaningNeg81 q) (meaning952 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 952 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_right (literal (valuationOf q) (951)) (literal (valuationOf q) (953)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 1 (meaning951 q) (meaning953 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 953 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-74, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-79, -81])
  have hm := merge_right (literal (valuationOf q) (952)) (literal (valuationOf q) (954)) (countLit q [-74, -76]) (countLit q [-79, -81]) (count953 q) 2 (meaning952 q) (meaning954 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 954 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E213.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112213
