import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_right (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 1 (meaning938 q) (meaning942 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 942 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_right (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 2 (meaning939 q) (meaning943 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 943 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_right (literal (valuationOf q) (940)) (literal (valuationOf q) (944)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 3 (meaning940 q) (meaning944 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 944 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_right (literal (valuationOf q) (941)) (literal (valuationOf q) (945)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 4 (meaning941 q) (meaning945 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 945 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_left (literal (valuationOf q) (931)) (literal (valuationOf q) (942)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 1 (meaning931 q) (meaning942 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 942 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 938 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (938)) (literal (valuationOf q) (943)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 1 1 (meaning931 q) (meaning938 q) (meaning943 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 938 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 938 = false ∨ valuation q 943 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (939)) (literal (valuationOf q) (944)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 1 2 (meaning931 q) (meaning939 q) (meaning944 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 939 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 939 = false ∨ valuation q 944 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (940)) (literal (valuationOf q) (945)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 1 3 (meaning931 q) (meaning940 q) (meaning945 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 940 = false ∨ valuation q 945 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (941)) (literal (valuationOf q) (946)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 1 4 (meaning931 q) (meaning941 q) (meaning946 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 941 = false ∨ valuation q 946 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (943)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 2 (meaning932 q) (meaning943 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 943 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 938 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (938)) (literal (valuationOf q) (944)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 2 1 (meaning932 q) (meaning938 q) (meaning944 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 938 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 938 = false ∨ valuation q 944 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (939)) (literal (valuationOf q) (945)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 2 2 (meaning932 q) (meaning939 q) (meaning945 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 939 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 939 = false ∨ valuation q 945 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (940)) (literal (valuationOf q) (946)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 2 3 (meaning932 q) (meaning940 q) (meaning946 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 940 = false ∨ valuation q 946 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (941)) (literal (valuationOf q) (947)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 2 4 (meaning932 q) (meaning941 q) (meaning947 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 941 = false ∨ valuation q 947 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 944 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_left (literal (valuationOf q) (933)) (literal (valuationOf q) (944)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 3 (meaning933 q) (meaning944 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 944 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 938 = false ∨ valuationOf q 945 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (938)) (literal (valuationOf q) (945)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 3 1 (meaning933 q) (meaning938 q) (meaning945 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 938 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 938 = false ∨ valuation q 945 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 939 = false ∨ valuationOf q 946 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (939)) (literal (valuationOf q) (946)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 3 2 (meaning933 q) (meaning939 q) (meaning946 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 939 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 939 = false ∨ valuation q 946 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (940)) (literal (valuationOf q) (947)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 3 3 (meaning933 q) (meaning940 q) (meaning947 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 940 = false ∨ valuation q 947 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true := by
  have hs : count942 q = (countLit q [-57, -60, -62]) + (countLit q [-65, -66, -68, -69]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62]) (l₂ := [-65, -66, -68, -69])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (941)) (literal (valuationOf q) (948)) (countLit q [-57, -60, -62]) (countLit q [-65, -66, -68, -69]) (count942 q) 3 4 (meaning933 q) (meaning941 q) (meaning948 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 941 = false ∨ valuation q 948 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (949)) (countLit q [-71]) (countLit q [-74]) (count949 q) 1 (meaningNeg74 q) (meaning949 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 949 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 949 = true := by
  have hs : count949 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (949)) (countLit q [-71]) (countLit q [-74]) (count949 q) 1 (meaningNeg71 q) (meaning949 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 949 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 74 = true ∨ valuationOf q 950 = true := by
  have hs : count949 q = (countLit q [-71]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (950)) (countLit q [-71]) (countLit q [-74]) (count949 q) 1 1 (meaningNeg71 q) (meaningNeg74 q) (meaning950 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 74 = true ∨ valuation q 950 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (951)) (countLit q [-77]) (countLit q [-78]) (count951 q) 1 (meaningNeg78 q) (meaning951 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 951 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (951)) (countLit q [-77]) (countLit q [-78]) (count951 q) 1 (meaningNeg77 q) (meaning951 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 951 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (952)) (countLit q [-77]) (countLit q [-78]) (count951 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning952 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 952 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (951)) (literal (valuationOf q) (953)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 1 (meaning951 q) (meaning953 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 953 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (952)) (literal (valuationOf q) (954)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 2 (meaning952 q) (meaning954 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 954 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (949)) (literal (valuationOf q) (953)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 1 (meaning949 q) (meaning953 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 953 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (951)) (literal (valuationOf q) (954)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 1 1 (meaning949 q) (meaning951 q) (meaning954 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 951 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 951 = false ∨ valuation q 954 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (952)) (literal (valuationOf q) (955)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 1 2 (meaning949 q) (meaning952 q) (meaning955 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 952 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 952 = false ∨ valuation q 955 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (950)) (literal (valuationOf q) (954)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 2 (meaning950 q) (meaning954 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 954 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count953 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count953 q) 2 1 (meaning950 q) (meaning951 q) (meaning955 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 951 = false ∨ valuation q 955 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E081.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112081
