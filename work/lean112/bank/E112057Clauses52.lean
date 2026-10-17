import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec52 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1665 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 7 2 (meaning1041 q) (meaning1060 q) (meaning1075 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1665 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1060 = false ∨ valuation q 1075 = true := counterClause1665 (baseVal q)

theorem counterClause1666 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 7 3 (meaning1041 q) (meaning1061 q) (meaning1076 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1666 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1061 = false ∨ valuation q 1076 = true := counterClause1666 (baseVal q)

theorem counterClause1667 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1077 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1077)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 7 4 (meaning1041 q) (meaning1062 q) (meaning1077 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1667 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1062 = false ∨ valuation q 1077 = true := counterClause1667 (baseVal q)

theorem counterClause1668 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1078 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1078)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 7 5 (meaning1041 q) (meaning1063 q) (meaning1078 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1668 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1063 = false ∨ valuation q 1078 = true := counterClause1668 (baseVal q)

theorem counterClause1669 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1079 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1064)) (literal (valuationOf q) (1079)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 7 6 (meaning1041 q) (meaning1064 q) (meaning1079 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1669 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1064 = false ∨ valuation q 1079 = true := counterClause1669 (baseVal q)

theorem counterClause1670 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1042)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 8 1 (meaning1042 q) (meaning1059 q) (meaning1075 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1670 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1059 = false ∨ valuation q 1075 = true := counterClause1670 (baseVal q)

theorem counterClause1671 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1042)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 8 2 (meaning1042 q) (meaning1060 q) (meaning1076 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1671 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1060 = false ∨ valuation q 1076 = true := counterClause1671 (baseVal q)

theorem counterClause1672 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1077 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1042)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1077)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 8 3 (meaning1042 q) (meaning1061 q) (meaning1077 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1672 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1061 = false ∨ valuation q 1077 = true := counterClause1672 (baseVal q)

theorem counterClause1673 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1078 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1042)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1078)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 8 4 (meaning1042 q) (meaning1062 q) (meaning1078 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1673 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1062 = false ∨ valuation q 1078 = true := counterClause1673 (baseVal q)

theorem counterClause1674 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1079 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1042)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1079)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 8 5 (meaning1042 q) (meaning1063 q) (meaning1079 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1674 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1063 = false ∨ valuation q 1079 = true := counterClause1674 (baseVal q)

theorem counterClause1675 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1083)) (countLit q [-95]) (countLit q [-96]) (count1083 q) 1 (meaningNeg96 q) (meaning1083 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1675 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1083 = true := counterClause1675 (baseVal q)

theorem counterClause1676 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1083)) (countLit q [-95]) (countLit q [-96]) (count1083 q) 1 (meaningNeg95 q) (meaning1083 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1676 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1083 = true := counterClause1676 (baseVal q)

theorem counterClause1677 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1084)) (countLit q [-95]) (countLit q [-96]) (count1083 q) 1 1 (meaningNeg95 q) (meaningNeg96 q) (meaning1084 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1677 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 96 = true ∨ valuation q 1084 = true := counterClause1677 (baseVal q)

theorem counterClause1678 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1085 = true := by
  have hs : count1085 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1085)) (countLit q [-97]) (countLit q [-101]) (count1085 q) 1 (meaningNeg101 q) (meaning1085 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1678 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1085 = true := counterClause1678 (baseVal q)

theorem counterClause1679 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1085 = true := by
  have hs : count1085 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1085)) (countLit q [-97]) (countLit q [-101]) (count1085 q) 1 (meaningNeg97 q) (meaning1085 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1679 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1085 = true := counterClause1679 (baseVal q)

theorem counterClause1680 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1086 = true := by
  have hs : count1085 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1086)) (countLit q [-97]) (countLit q [-101]) (count1085 q) 1 1 (meaningNeg97 q) (meaningNeg101 q) (meaning1086 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1680 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 1086 = true := counterClause1680 (baseVal q)

theorem counterClause1681 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_right (literal (valuationOf q) (1085)) (literal (valuationOf q) (1087)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 1 (meaning1085 q) (meaning1087 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1681 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1087 = true := counterClause1681 (baseVal q)

theorem counterClause1682 (q : Nat → Bool) : valuationOf q 1086 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_right (literal (valuationOf q) (1086)) (literal (valuationOf q) (1088)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 2 (meaning1086 q) (meaning1088 q) hs
  change valuationOf q 1086 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1682 (q : Snake 81) (h : Conditions q) : valuation q 1086 = false ∨ valuation q 1088 = true := counterClause1682 (baseVal q)

theorem counterClause1683 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_left (literal (valuationOf q) (1083)) (literal (valuationOf q) (1087)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 1 (meaning1083 q) (meaning1087 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1683 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1087 = true := counterClause1683 (baseVal q)

theorem counterClause1684 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_two (literal (valuationOf q) (1083)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1088)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 1 1 (meaning1083 q) (meaning1085 q) (meaning1088 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1684 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1085 = false ∨ valuation q 1088 = true := counterClause1684 (baseVal q)

theorem counterClause1685 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_two (literal (valuationOf q) (1083)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1089)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 1 2 (meaning1083 q) (meaning1086 q) (meaning1089 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1685 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1086 = false ∨ valuation q 1089 = true := counterClause1685 (baseVal q)

theorem counterClause1686 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_left (literal (valuationOf q) (1084)) (literal (valuationOf q) (1088)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 2 (meaning1084 q) (meaning1088 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1686 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1088 = true := counterClause1686 (baseVal q)

theorem counterClause1687 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_two (literal (valuationOf q) (1084)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1089)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 2 1 (meaning1084 q) (meaning1085 q) (meaning1089 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1687 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1085 = false ∨ valuation q 1089 = true := counterClause1687 (baseVal q)

theorem counterClause1688 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-95, -96]) + (countLit q [-97, -101]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-97, -101])
  have hm := merge_two (literal (valuationOf q) (1084)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1090)) (countLit q [-95, -96]) (countLit q [-97, -101]) (count1087 q) 2 2 (meaning1084 q) (meaning1086 q) (meaning1090 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1688 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1086 = false ∨ valuation q 1090 = true := counterClause1688 (baseVal q)

theorem counterClause1689 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1091 = true := by
  have hs : count1091 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1091)) (countLit q [-103]) (countLit q [-105]) (count1091 q) 1 (meaningNeg105 q) (meaning1091 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1689 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1091 = true := counterClause1689 (baseVal q)

theorem counterClause1690 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1091 = true := by
  have hs : count1091 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1091)) (countLit q [-103]) (countLit q [-105]) (count1091 q) 1 (meaningNeg103 q) (meaning1091 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1690 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1091 = true := counterClause1690 (baseVal q)

theorem counterClause1691 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1092 = true := by
  have hs : count1091 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1092)) (countLit q [-103]) (countLit q [-105]) (count1091 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1092 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1691 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1092 = true := counterClause1691 (baseVal q)

theorem counterClause1692 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1093 = true := by
  have hs : count1093 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1093)) (countLit q [-107]) (countLit q [-109]) (count1093 q) 1 (meaningNeg109 q) (meaning1093 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1692 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1093 = true := counterClause1692 (baseVal q)

theorem counterClause1693 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1093 = true := by
  have hs : count1093 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1093)) (countLit q [-107]) (countLit q [-109]) (count1093 q) 1 (meaningNeg107 q) (meaning1093 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1693 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1093 = true := counterClause1693 (baseVal q)

theorem counterClause1694 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1094 = true := by
  have hs : count1093 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1094)) (countLit q [-107]) (countLit q [-109]) (count1093 q) 1 1 (meaningNeg107 q) (meaningNeg109 q) (meaning1094 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1094 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1694 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 1094 = true := counterClause1694 (baseVal q)

theorem counterClause1695 (q : Nat → Bool) : valuationOf q 1093 = false ∨ valuationOf q 1095 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1093)) (literal (valuationOf q) (1095)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 1 (meaning1093 q) (meaning1095 q) hs
  change valuationOf q 1093 = false ∨ valuationOf q 1095 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1695 (q : Snake 81) (h : Conditions q) : valuation q 1093 = false ∨ valuation q 1095 = true := counterClause1695 (baseVal q)

theorem counterClause1696 (q : Nat → Bool) : valuationOf q 1094 = false ∨ valuationOf q 1096 = true := by
  have hs : count1095 q = (countLit q [-103, -105]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1094)) (literal (valuationOf q) (1096)) (countLit q [-103, -105]) (countLit q [-107, -109]) (count1095 q) 2 (meaning1094 q) (meaning1096 q) hs
  change valuationOf q 1094 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1696 (q : Snake 81) (h : Conditions q) : valuation q 1094 = false ∨ valuation q 1096 = true := counterClause1696 (baseVal q)

theorem block52 (q : Snake 81) (h : Conditions q) : B112E057.Block52 (valuation q) :=
  ⟨clause1665 q h, clause1666 q h, clause1667 q h, clause1668 q h, clause1669 q h, clause1670 q h, clause1671 q h, clause1672 q h, clause1673 q h, clause1674 q h, clause1675 q h, clause1676 q h, clause1677 q h, clause1678 q h, clause1679 q h, clause1680 q h, clause1681 q h, clause1682 q h, clause1683 q h, clause1684 q h, clause1685 q h, clause1686 q h, clause1687 q h, clause1688 q h, clause1689 q h, clause1690 q h, clause1691 q h, clause1692 q h, clause1693 q h, clause1694 q h, clause1695 q h, clause1696 q h⟩

end
end Snake9.Regrowth.E112057
