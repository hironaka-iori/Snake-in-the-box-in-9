import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1077 = true := by
  have hs : count1075 q = (countLit q [-113, -115]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-113, -115]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1077)) (countLit q [-113, -115]) (countLit q [-117, -119]) (count1075 q) 1 2 (meaning1071 q) (meaning1074 q) (meaning1077 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1074 = false ∨ valuation q 1077 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1076 = true := by
  have hs : count1075 q = (countLit q [-113, -115]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-113, -115]) (l₂ := [-117, -119])
  have hm := merge_left (literal (valuationOf q) (1072)) (literal (valuationOf q) (1076)) (countLit q [-113, -115]) (countLit q [-117, -119]) (count1075 q) 2 (meaning1072 q) (meaning1076 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1076 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1077 = true := by
  have hs : count1075 q = (countLit q [-113, -115]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-113, -115]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1077)) (countLit q [-113, -115]) (countLit q [-117, -119]) (count1075 q) 2 1 (meaning1072 q) (meaning1073 q) (meaning1077 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1073 = false ∨ valuation q 1077 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1078 = true := by
  have hs : count1075 q = (countLit q [-113, -115]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-113, -115]) (l₂ := [-117, -119])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1078)) (countLit q [-113, -115]) (countLit q [-117, -119]) (count1075 q) 2 2 (meaning1072 q) (meaning1074 q) (meaning1078 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1074 = false ∨ valuation q 1078 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-122]) + (countLit q [-124]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-124])
  have hm := merge_right (literal (valuationOf q) (-124)) (literal (valuationOf q) (1079)) (countLit q [-122]) (countLit q [-124]) (count1079 q) 1 (meaningNeg124 q) (meaning1079 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1079 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1079 = true := by
  have hs : count1079 q = (countLit q [-122]) + (countLit q [-124]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-124])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1079)) (countLit q [-122]) (countLit q [-124]) (count1079 q) 1 (meaningNeg122 q) (meaning1079 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1079 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 124 = true ∨ valuationOf q 1080 = true := by
  have hs : count1079 q = (countLit q [-122]) + (countLit q [-124]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-124])
  have hm := merge_two (literal (valuationOf q) (-122)) (literal (valuationOf q) (-124)) (literal (valuationOf q) (1080)) (countLit q [-122]) (countLit q [-124]) (count1079 q) 1 1 (meaningNeg122 q) (meaningNeg124 q) (meaning1080 q) hs
  change (! (valuationOf q 122)) = false ∨ (! (valuationOf q 124)) = false ∨ valuationOf q 1080 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 124 = true ∨ valuation q 1080 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 127 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-126]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-126]) (l₂ := [-127])
  have hm := merge_right (literal (valuationOf q) (-127)) (literal (valuationOf q) (1081)) (countLit q [-126]) (countLit q [-127]) (count1081 q) 1 (meaningNeg127 q) (meaning1081 q) hs
  change (! (valuationOf q 127)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 127 = true ∨ valuation q 1081 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1081 = true := by
  have hs : count1081 q = (countLit q [-126]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-126]) (l₂ := [-127])
  have hm := merge_left (literal (valuationOf q) (-126)) (literal (valuationOf q) (1081)) (countLit q [-126]) (countLit q [-127]) (count1081 q) 1 (meaningNeg126 q) (meaning1081 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1081 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 127 = true ∨ valuationOf q 1082 = true := by
  have hs : count1081 q = (countLit q [-126]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-126]) (l₂ := [-127])
  have hm := merge_two (literal (valuationOf q) (-126)) (literal (valuationOf q) (-127)) (literal (valuationOf q) (1082)) (countLit q [-126]) (countLit q [-127]) (count1081 q) 1 1 (meaningNeg126 q) (meaningNeg127 q) (meaning1082 q) hs
  change (! (valuationOf q 126)) = false ∨ (! (valuationOf q 127)) = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 1082 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1081 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_right (literal (valuationOf q) (1081)) (literal (valuationOf q) (1083)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 1 (meaning1081 q) (meaning1083 q) hs
  change valuationOf q 1081 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1081 = false ∨ valuation q 1083 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1082 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_right (literal (valuationOf q) (1082)) (literal (valuationOf q) (1084)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 2 (meaning1082 q) (meaning1084 q) hs
  change valuationOf q 1082 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1082 = false ∨ valuation q 1084 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1083 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_left (literal (valuationOf q) (1079)) (literal (valuationOf q) (1083)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 1 (meaning1079 q) (meaning1083 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1083 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1084)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 1 1 (meaning1079 q) (meaning1081 q) (meaning1084 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1081 = false ∨ valuation q 1084 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1079)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1085)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 1 2 (meaning1079 q) (meaning1082 q) (meaning1085 q) hs
  change valuationOf q 1079 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1079 = false ∨ valuation q 1082 = false ∨ valuation q 1085 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1084 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_left (literal (valuationOf q) (1080)) (literal (valuationOf q) (1084)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 2 (meaning1080 q) (meaning1084 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1084 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1081)) (literal (valuationOf q) (1085)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 2 1 (meaning1080 q) (meaning1081 q) (meaning1085 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1081 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1081 = false ∨ valuation q 1085 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true := by
  have hs : count1083 q = (countLit q [-122, -124]) + (countLit q [-126, -127]) := List.countP_append (p := literal q) (l₁ := [-122, -124]) (l₂ := [-126, -127])
  have hm := merge_two (literal (valuationOf q) (1080)) (literal (valuationOf q) (1082)) (literal (valuationOf q) (1086)) (countLit q [-122, -124]) (countLit q [-126, -127]) (count1083 q) 2 2 (meaning1080 q) (meaning1082 q) (meaning1086 q) hs
  change valuationOf q 1080 = false ∨ valuationOf q 1082 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1080 = false ∨ valuation q 1082 = false ∨ valuation q 1086 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1083 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1083)) (literal (valuationOf q) (1087)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 1 (meaning1083 q) (meaning1087 q) hs
  change valuationOf q 1083 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1083 = false ∨ valuation q 1087 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1084 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1084)) (literal (valuationOf q) (1088)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 2 (meaning1084 q) (meaning1088 q) hs
  change valuationOf q 1084 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1084 = false ∨ valuation q 1088 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1085 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1085)) (literal (valuationOf q) (1089)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 3 (meaning1085 q) (meaning1089 q) hs
  change valuationOf q 1085 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1085 = false ∨ valuation q 1089 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1086 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_right (literal (valuationOf q) (1086)) (literal (valuationOf q) (1090)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 4 (meaning1086 q) (meaning1090 q) hs
  change valuationOf q 1086 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1086 = false ∨ valuation q 1090 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1087 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1075)) (literal (valuationOf q) (1087)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 1 (meaning1075 q) (meaning1087 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1087 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1088)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 1 1 (meaning1075 q) (meaning1083 q) (meaning1088 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1083 = false ∨ valuation q 1088 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1089)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 1 2 (meaning1075 q) (meaning1084 q) (meaning1089 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1084 = false ∨ valuation q 1089 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1090)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 1 3 (meaning1075 q) (meaning1085 q) (meaning1090 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1085 = false ∨ valuation q 1090 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1091)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 1 4 (meaning1075 q) (meaning1086 q) (meaning1091 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1086 = false ∨ valuation q 1091 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1076)) (literal (valuationOf q) (1088)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 2 (meaning1076 q) (meaning1088 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1088 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1089)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 2 1 (meaning1076 q) (meaning1083 q) (meaning1089 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1083 = false ∨ valuation q 1089 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1090)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 2 2 (meaning1076 q) (meaning1084 q) (meaning1090 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1084 = false ∨ valuation q 1090 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1091)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 2 3 (meaning1076 q) (meaning1085 q) (meaning1091 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1085 = false ∨ valuation q 1091 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-113, -115, -117, -119]) + (countLit q [-122, -124, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-113, -115, -117, -119]) (l₂ := [-122, -124, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1077)) (literal (valuationOf q) (1089)) (countLit q [-113, -115, -117, -119]) (countLit q [-122, -124, -126, -127]) (count1087 q) 3 (meaning1077 q) (meaning1089 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1089 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E260.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112260
