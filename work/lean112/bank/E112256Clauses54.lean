import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1124)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 10 4 (meaning1041 q) (meaning1098 q) (meaning1124 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1098 = false ∨ valuation q 1124 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 7 14 (meaning973 q) (meaning1124 q) (meaning1152 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1124 = false ∨ valuation q 1152 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 8 13 (meaning974 q) (meaning1123 q) (meaning1152 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1123 = false ∨ valuation q 1152 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1122)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 9 12 (meaning975 q) (meaning1122 q) (meaning1152 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1122 = false ∨ valuation q 1152 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (976)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 10 11 (meaning976 q) (meaning1121 q) (meaning1152 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 1121 = false ∨ valuation q 1152 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 11 10 (meaning977 q) (meaning1120 q) (meaning1152 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 1120 = false ∨ valuation q 1152 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (978)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 12 9 (meaning978 q) (meaning1119 q) (meaning1152 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 1119 = false ∨ valuation q 1152 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 1118 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (979)) (literal (valuationOf q) (1118)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 13 8 (meaning979 q) (meaning1118 q) (meaning1152 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 1118 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 1118 = false ∨ valuation q 1152 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1117)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 14 7 (meaning980 q) (meaning1117 q) (meaning1152 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1117 = false ∨ valuation q 1152 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1116 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1116)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 15 6 (meaning981 q) (meaning1116 q) (meaning1152 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1116 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1116 = false ∨ valuation q 1152 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 982 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1152 = true := by
  have hs : count1132 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) + (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (l₂ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (982)) (literal (valuationOf q) (1115)) (literal (valuationOf q) (1152)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1132 q) 16 5 (meaning982 q) (meaning1115 q) (meaning1152 q) hs
  change valuationOf q 982 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 982 = false ∨ valuation q 1115 = false ∨ valuation q 1152 = true := counterClause1739 (baseVal q)

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1152 = false := by
  rw [value1152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1132 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 1530 = true := by
  have hs : count1529 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (1530)) (countLit q [-3]) (countLit q [-4]) (count1529 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning1530 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 1530 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-3, -4]) + (countLit q [-6, -8]) := List.countP_append (p := literal q) (l₁ := [-3, -4]) (l₂ := [-6, -8])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-3, -4]) (countLit q [-6, -8]) (count1533 q) 2 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1540)) (countLit q [-13]) (countLit q [-16]) (count1539 q) 1 1 (meaningNeg13 q) (meaningNeg16 q) (meaning1540 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 1540 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-9, -12]) + (countLit q [-13, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -12]) (l₂ := [-13, -16])
  have hm := merge_right (literal (valuationOf q) (1540)) (literal (valuationOf q) (1542)) (countLit q [-9, -12]) (countLit q [-13, -16]) (count1541 q) 2 (meaning1540 q) (meaning1542 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1542 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-3, -4, -6, -8]) + (countLit q [-9, -12, -13, -16]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8]) (l₂ := [-9, -12, -13, -16])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1548)) (countLit q [-3, -4, -6, -8]) (countLit q [-9, -12, -13, -16]) (count1545 q) 2 2 (meaning1534 q) (meaning1542 q) (meaning1548 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1542 = false ∨ valuation q 1548 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-22]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1556)) (countLit q [-22]) (countLit q [-24]) (count1555 q) 1 1 (meaningNeg22 q) (meaningNeg24 q) (meaning1556 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 1556 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-17, -20]) + (countLit q [-22, -24]) := List.countP_append (p := literal q) (l₁ := [-17, -20]) (l₂ := [-22, -24])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (countLit q [-17, -20]) (countLit q [-22, -24]) (count1557 q) 2 (meaning1556 q) (meaning1558 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1561 = true := by
  have hs : count1561 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1561)) (countLit q [-26]) (countLit q [-27]) (count1561 q) 1 (meaningNeg27 q) (meaning1561 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1561 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1565 q = (countLit q [-26, -27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-26, -27]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-26, -27]) (countLit q [-29, -31]) (count1565 q) 1 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true := by
  have hs : count1569 q = (countLit q [-17, -20, -22, -24]) + (countLit q [-26, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -24]) (l₂ := [-26, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (countLit q [-17, -20, -22, -24]) (countLit q [-26, -27, -29, -31]) (count1569 q) 2 1 (meaning1558 q) (meaning1565 q) (meaning1571 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1565 = false ∨ valuation q 1571 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1583 = true := by
  have hs : count1577 q = (countLit q [-3, -4, -6, -8, -9, -12, -13, -16]) + (countLit q [-17, -20, -22, -24, -26, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -9, -12, -13, -16]) (l₂ := [-17, -20, -22, -24, -26, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1583)) (countLit q [-3, -4, -6, -8, -9, -12, -13, -16]) (countLit q [-17, -20, -22, -24, -26, -27, -29, -31]) (count1577 q) 4 3 (meaning1548 q) (meaning1571 q) (meaning1583 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1571 = false ∨ valuation q 1583 = true := counterClause1751 (baseVal q)

theorem counterClause1752 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-32]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1594)) (countLit q [-32]) (countLit q [-35]) (count1593 q) 1 1 (meaningNeg32 q) (meaningNeg35 q) (meaning1594 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 35 = true ∨ valuation q 1594 = true := counterClause1752 (baseVal q)

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1595)) (countLit q [-37]) (countLit q [-38]) (count1595 q) 1 (meaningNeg37 q) (meaning1595 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1595 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1599 = true := by
  have hs : count1597 q = (countLit q [-32, -35]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-32, -35]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1599)) (countLit q [-32, -35]) (countLit q [-37, -38]) (count1597 q) 2 1 (meaning1594 q) (meaning1595 q) (meaning1599 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1595 = false ∨ valuation q 1599 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1601)) (countLit q [-39]) (countLit q [-40]) (count1601 q) 1 (meaningNeg40 q) (meaning1601 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1601 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-39, -40]) + (countLit q [-46, -48]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-46, -48])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-39, -40]) (countLit q [-46, -48]) (count1605 q) 1 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1612 = true := by
  have hs : count1609 q = (countLit q [-32, -35, -37, -38]) + (countLit q [-39, -40, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38]) (l₂ := [-39, -40, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (countLit q [-32, -35, -37, -38]) (countLit q [-39, -40, -46, -48]) (count1609 q) 3 1 (meaning1599 q) (meaning1605 q) (meaning1612 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1605 = false ∨ valuation q 1612 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1619)) (countLit q [-52]) (countLit q [-54]) (count1619 q) 1 (meaningNeg54 q) (meaning1619 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1619 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-50, -51]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-50, -51]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1621)) (countLit q [-50, -51]) (countLit q [-52, -54]) (count1621 q) 1 (meaning1619 q) (meaning1621 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1621 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1625)) (countLit q [-55]) (countLit q [-56]) (count1625 q) 1 (meaningNeg56 q) (meaning1625 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1625 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E256.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112256
