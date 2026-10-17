import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 942 = true := by
  have hs : count942 q = (countLit q [-66, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-68, -71])
  have hm := merge_left (literal (valuationOf q) (938)) (literal (valuationOf q) (942)) (countLit q [-66, -67]) (countLit q [-68, -71]) (count942 q) 1 (meaning938 q) (meaning942 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 942 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 940 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-66, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (940)) (literal (valuationOf q) (943)) (countLit q [-66, -67]) (countLit q [-68, -71]) (count942 q) 1 1 (meaning938 q) (meaning940 q) (meaning943 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 940 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 940 = false ∨ valuation q 943 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count942 q = (countLit q [-66, -67]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-68, -71])
  have hm := merge_left (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-66, -67]) (countLit q [-68, -71]) (count942 q) 2 (meaning939 q) (meaning943 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 943 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 946 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_right (literal (valuationOf q) (942)) (literal (valuationOf q) (946)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 1 (meaning942 q) (meaning946 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 946 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 947 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_right (literal (valuationOf q) (943)) (literal (valuationOf q) (947)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 2 (meaning943 q) (meaning947 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 947 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 946 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (946)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 1 (meaning935 q) (meaning946 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 946 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 942 = false ∨ valuationOf q 947 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (942)) (literal (valuationOf q) (947)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 1 1 (meaning935 q) (meaning942 q) (meaning947 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 942 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 942 = false ∨ valuation q 947 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 947 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_left (literal (valuationOf q) (936)) (literal (valuationOf q) (947)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 2 (meaning936 q) (meaning947 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 947 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 942 = false ∨ valuationOf q 948 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (942)) (literal (valuationOf q) (948)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 2 1 (meaning936 q) (meaning942 q) (meaning948 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 942 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 942 = false ∨ valuation q 948 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 948 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_left (literal (valuationOf q) (937)) (literal (valuationOf q) (948)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 3 (meaning937 q) (meaning948 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 948 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true := by
  have hs : count946 q = (countLit q [-58, -60, -61]) + (countLit q [-66, -67, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61]) (l₂ := [-66, -67, -68, -71])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (942)) (literal (valuationOf q) (949)) (countLit q [-58, -60, -61]) (countLit q [-66, -67, -68, -71]) (count946 q) 3 1 (meaning937 q) (meaning942 q) (meaning949 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 942 = false ∨ valuation q 949 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (953)) (countLit q [-72]) (countLit q [-74]) (count953 q) 1 (meaningNeg74 q) (meaning953 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 953 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 953 = true := by
  have hs : count953 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (953)) (countLit q [-72]) (countLit q [-74]) (count953 q) 1 (meaningNeg72 q) (meaning953 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 953 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 954 = true := by
  have hs : count953 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (954)) (countLit q [-72]) (countLit q [-74]) (count953 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning954 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 954 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 955 = true := by
  have hs : count955 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (955)) (countLit q [-78]) (countLit q [-79]) (count955 q) 1 (meaningNeg78 q) (meaning955 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 955 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 956 = true := by
  have hs : count955 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (956)) (countLit q [-78]) (countLit q [-79]) (count955 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning956 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 956 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-72, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (955)) (literal (valuationOf q) (957)) (countLit q [-72, -74]) (countLit q [-78, -79]) (count957 q) 1 (meaning955 q) (meaning957 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 957 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 956 = false ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-72, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (956)) (literal (valuationOf q) (958)) (countLit q [-72, -74]) (countLit q [-78, -79]) (count957 q) 2 (meaning956 q) (meaning958 q) hs
  change valuationOf q 956 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 956 = false ∨ valuation q 958 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-72, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (953)) (literal (valuationOf q) (957)) (countLit q [-72, -74]) (countLit q [-78, -79]) (count957 q) 1 (meaning953 q) (meaning957 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 957 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 953 = false ∨ valuationOf q 955 = false ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-72, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (953)) (literal (valuationOf q) (955)) (literal (valuationOf q) (958)) (countLit q [-72, -74]) (countLit q [-78, -79]) (count957 q) 1 1 (meaning953 q) (meaning955 q) (meaning958 q) hs
  change valuationOf q 953 = false ∨ valuationOf q 955 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 953 = false ∨ valuation q 955 = false ∨ valuation q 958 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 958 = true := by
  have hs : count957 q = (countLit q [-72, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (954)) (literal (valuationOf q) (958)) (countLit q [-72, -74]) (countLit q [-78, -79]) (count957 q) 2 (meaning954 q) (meaning958 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 958 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 954 = false ∨ valuationOf q 955 = false ∨ valuationOf q 959 = true := by
  have hs : count957 q = (countLit q [-72, -74]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -74]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (954)) (literal (valuationOf q) (955)) (literal (valuationOf q) (959)) (countLit q [-72, -74]) (countLit q [-78, -79]) (count957 q) 2 1 (meaning954 q) (meaning955 q) (meaning959 q) hs
  change valuationOf q 954 = false ∨ valuationOf q 955 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 954 = false ∨ valuation q 955 = false ∨ valuation q 959 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (961)) (countLit q [-81]) (countLit q [-82]) (count961 q) 1 (meaningNeg82 q) (meaning961 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 961 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 961 = true := by
  have hs : count961 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (961)) (countLit q [-81]) (countLit q [-82]) (count961 q) 1 (meaningNeg81 q) (meaning961 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 961 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (963)) (countLit q [-84]) (countLit q [-87]) (count963 q) 1 (meaningNeg87 q) (meaning963 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 963 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (963)) (countLit q [-84]) (countLit q [-87]) (count963 q) 1 (meaningNeg84 q) (meaning963 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 963 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 87 = true ∨ valuationOf q 964 = true := by
  have hs : count963 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (964)) (countLit q [-84]) (countLit q [-87]) (count963 q) 1 1 (meaningNeg84 q) (meaningNeg87 q) (meaning964 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 964 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-81, -82]) + (countLit q [-84, -87]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-84, -87])
  have hm := merge_right (literal (valuationOf q) (963)) (literal (valuationOf q) (965)) (countLit q [-81, -82]) (countLit q [-84, -87]) (count965 q) 1 (meaning963 q) (meaning965 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 965 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-81, -82]) + (countLit q [-84, -87]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-84, -87])
  have hm := merge_right (literal (valuationOf q) (964)) (literal (valuationOf q) (966)) (countLit q [-81, -82]) (countLit q [-84, -87]) (count965 q) 2 (meaning964 q) (meaning966 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 966 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-81, -82]) + (countLit q [-84, -87]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-84, -87])
  have hm := merge_left (literal (valuationOf q) (961)) (literal (valuationOf q) (965)) (countLit q [-81, -82]) (countLit q [-84, -87]) (count965 q) 1 (meaning961 q) (meaning965 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 965 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 963 = false ∨ valuationOf q 966 = true := by
  have hs : count965 q = (countLit q [-81, -82]) + (countLit q [-84, -87]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-84, -87])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (963)) (literal (valuationOf q) (966)) (countLit q [-81, -82]) (countLit q [-84, -87]) (count965 q) 1 1 (meaning961 q) (meaning963 q) (meaning966 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 963 = false ∨ valuationOf q 966 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 963 = false ∨ valuation q 966 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 964 = false ∨ valuationOf q 967 = true := by
  have hs : count965 q = (countLit q [-81, -82]) + (countLit q [-84, -87]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-84, -87])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (964)) (literal (valuationOf q) (967)) (countLit q [-81, -82]) (countLit q [-84, -87]) (count965 q) 1 2 (meaning961 q) (meaning964 q) (meaning967 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 964 = false ∨ valuationOf q 967 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 964 = false ∨ valuation q 967 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E159.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112159
