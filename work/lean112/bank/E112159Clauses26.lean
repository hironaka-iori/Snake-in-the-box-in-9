import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 969 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_right (literal (valuationOf q) (965)) (literal (valuationOf q) (969)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 1 (meaning965 q) (meaning969 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 969 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 966 = false ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_right (literal (valuationOf q) (966)) (literal (valuationOf q) (970)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 2 (meaning966 q) (meaning970 q) hs
  change valuationOf q 966 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 966 = false ∨ valuation q 970 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 969 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_left (literal (valuationOf q) (957)) (literal (valuationOf q) (969)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 1 (meaning957 q) (meaning969 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 969 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 969 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 965 = false ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (965)) (literal (valuationOf q) (970)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 1 1 (meaning957 q) (meaning965 q) (meaning970 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 965 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 965 = false ∨ valuation q 970 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 966 = false ∨ valuationOf q 971 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (966)) (literal (valuationOf q) (971)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 1 2 (meaning957 q) (meaning966 q) (meaning971 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 966 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 966 = false ∨ valuation q 971 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 957 = false ∨ valuationOf q 967 = false ∨ valuationOf q 972 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (957)) (literal (valuationOf q) (967)) (literal (valuationOf q) (972)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 1 3 (meaning957 q) (meaning967 q) (meaning972 q) hs
  change valuationOf q 957 = false ∨ valuationOf q 967 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 957 = false ∨ valuation q 967 = false ∨ valuation q 972 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 970 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_left (literal (valuationOf q) (958)) (literal (valuationOf q) (970)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 2 (meaning958 q) (meaning970 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 970 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 970 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 965 = false ∨ valuationOf q 971 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (965)) (literal (valuationOf q) (971)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 2 1 (meaning958 q) (meaning965 q) (meaning971 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 965 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 965 = false ∨ valuation q 971 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 958 = false ∨ valuationOf q 966 = false ∨ valuationOf q 972 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (958)) (literal (valuationOf q) (966)) (literal (valuationOf q) (972)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 2 2 (meaning958 q) (meaning966 q) (meaning972 q) hs
  change valuationOf q 958 = false ∨ valuationOf q 966 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 958 = false ∨ valuation q 966 = false ∨ valuation q 972 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 971 = true := by
  have hs : count969 q = (countLit q [-72, -74, -78, -79]) + (countLit q [-81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -78, -79]) (l₂ := [-81, -82, -84, -87])
  have hm := merge_left (literal (valuationOf q) (959)) (literal (valuationOf q) (971)) (countLit q [-72, -74, -78, -79]) (countLit q [-81, -82, -84, -87]) (count969 q) 3 (meaning959 q) (meaning971 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 971 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 969 = false ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_right (literal (valuationOf q) (969)) (literal (valuationOf q) (977)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 1 (meaning969 q) (meaning977 q) hs
  change valuationOf q 969 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 969 = false ∨ valuation q 977 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 970 = false ∨ valuationOf q 978 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_right (literal (valuationOf q) (970)) (literal (valuationOf q) (978)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 2 (meaning970 q) (meaning978 q) hs
  change valuationOf q 970 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 970 = false ∨ valuation q 978 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 971 = false ∨ valuationOf q 979 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_right (literal (valuationOf q) (971)) (literal (valuationOf q) (979)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 3 (meaning971 q) (meaning979 q) hs
  change valuationOf q 971 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 971 = false ∨ valuation q 979 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 980 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_right (literal (valuationOf q) (972)) (literal (valuationOf q) (980)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 4 (meaning972 q) (meaning980 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 980 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 969 = false ∨ valuationOf q 978 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (969)) (literal (valuationOf q) (978)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 1 1 (meaning946 q) (meaning969 q) (meaning978 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 969 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 969 = false ∨ valuation q 978 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 970 = false ∨ valuationOf q 979 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (970)) (literal (valuationOf q) (979)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 1 2 (meaning946 q) (meaning970 q) (meaning979 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 970 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 970 = false ∨ valuation q 979 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 971 = false ∨ valuationOf q 980 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (971)) (literal (valuationOf q) (980)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 1 3 (meaning946 q) (meaning971 q) (meaning980 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 971 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 971 = false ∨ valuation q 980 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 978 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_left (literal (valuationOf q) (947)) (literal (valuationOf q) (978)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 2 (meaning947 q) (meaning978 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 978 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (969)) (literal (valuationOf q) (979)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 2 1 (meaning947 q) (meaning969 q) (meaning979 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 969 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 969 = false ∨ valuation q 979 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 970 = false ∨ valuationOf q 980 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (970)) (literal (valuationOf q) (980)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 2 2 (meaning947 q) (meaning970 q) (meaning980 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 970 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 970 = false ∨ valuation q 980 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 979 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_left (literal (valuationOf q) (948)) (literal (valuationOf q) (979)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 3 (meaning948 q) (meaning979 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 979 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (969)) (literal (valuationOf q) (980)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 3 1 (meaning948 q) (meaning969 q) (meaning980 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 969 = false ∨ valuation q 980 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 970 = false ∨ valuationOf q 981 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (970)) (literal (valuationOf q) (981)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 3 2 (meaning948 q) (meaning970 q) (meaning981 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 970 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 970 = false ∨ valuation q 981 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 980 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_left (literal (valuationOf q) (949)) (literal (valuationOf q) (980)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 4 (meaning949 q) (meaning980 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 980 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 970 = false ∨ valuationOf q 982 = true := by
  have hs : count977 q = (countLit q [-58, -60, -61, -66, -67, -68, -71]) + (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71]) (l₂ := [-72, -74, -78, -79, -81, -82, -84, -87])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (970)) (literal (valuationOf q) (982)) (countLit q [-58, -60, -61, -66, -67, -68, -71]) (countLit q [-72, -74, -78, -79, -81, -82, -84, -87]) (count977 q) 4 2 (meaning949 q) (meaning970 q) (meaning982 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 970 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 970 = false ∨ valuation q 982 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-90]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (992)) (countLit q [-90]) (countLit q [-94]) (count992 q) 1 (meaningNeg94 q) (meaning992 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 992 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 992 = true := by
  have hs : count992 q = (countLit q [-90]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (992)) (countLit q [-90]) (countLit q [-94]) (count992 q) 1 (meaningNeg90 q) (meaning992 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 992 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 94 = true ∨ valuationOf q 993 = true := by
  have hs : count992 q = (countLit q [-90]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (993)) (countLit q [-90]) (countLit q [-94]) (count992 q) 1 1 (meaningNeg90 q) (meaningNeg94 q) (meaning993 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 94 = true ∨ valuation q 993 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 992 = false ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_right (literal (valuationOf q) (992)) (literal (valuationOf q) (994)) (countLit q [-88]) (countLit q [-90, -94]) (count994 q) 1 (meaning992 q) (meaning994 q) hs
  change valuationOf q 992 = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 992 = false ∨ valuation q 994 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 993 = false ∨ valuationOf q 995 = true := by
  have hs : count994 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_right (literal (valuationOf q) (993)) (literal (valuationOf q) (995)) (countLit q [-88]) (countLit q [-90, -94]) (count994 q) 2 (meaning993 q) (meaning995 q) hs
  change valuationOf q 993 = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 993 = false ∨ valuation q 995 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 994 = true := by
  have hs : count994 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (994)) (countLit q [-88]) (countLit q [-90, -94]) (count994 q) 1 (meaningNeg88 q) (meaning994 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 994 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 992 = false ∨ valuationOf q 995 = true := by
  have hs : count994 q = (countLit q [-88]) + (countLit q [-90, -94]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -94])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (992)) (literal (valuationOf q) (995)) (countLit q [-88]) (countLit q [-90, -94]) (count994 q) 1 1 (meaningNeg88 q) (meaning992 q) (meaning995 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 992 = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 992 = false ∨ valuation q 995 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E159.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112159
