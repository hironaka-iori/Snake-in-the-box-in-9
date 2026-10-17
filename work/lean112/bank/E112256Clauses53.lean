import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1697 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1121)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 8 (meaning1034 q) (meaning1102 q) (meaning1121 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1102 = false ∨ valuation q 1121 = true := counterClause1697 (baseVal q)

theorem counterClause1698 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1122)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 3 9 (meaning1034 q) (meaning1103 q) (meaning1122 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1103 = false ∨ valuation q 1122 = true := counterClause1698 (baseVal q)

theorem counterClause1699 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1117 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1117)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 3 (meaning1035 q) (meaning1097 q) (meaning1117 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1097 = false ∨ valuation q 1117 = true := counterClause1699 (baseVal q)

theorem counterClause1700 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1118)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 4 (meaning1035 q) (meaning1098 q) (meaning1118 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1098 = false ∨ valuation q 1118 = true := counterClause1700 (baseVal q)

theorem counterClause1701 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1119)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 5 (meaning1035 q) (meaning1099 q) (meaning1119 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1099 = false ∨ valuation q 1119 = true := counterClause1701 (baseVal q)

theorem counterClause1702 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1120)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 6 (meaning1035 q) (meaning1100 q) (meaning1120 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1100 = false ∨ valuation q 1120 = true := counterClause1702 (baseVal q)

theorem counterClause1703 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1121)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 7 (meaning1035 q) (meaning1101 q) (meaning1121 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1101 = false ∨ valuation q 1121 = true := counterClause1703 (baseVal q)

theorem counterClause1704 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1122)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 8 (meaning1035 q) (meaning1102 q) (meaning1122 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1102 = false ∨ valuation q 1122 = true := counterClause1704 (baseVal q)

theorem counterClause1705 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1123)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 9 (meaning1035 q) (meaning1103 q) (meaning1123 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1103 = false ∨ valuation q 1123 = true := counterClause1705 (baseVal q)

theorem counterClause1706 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1124)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 4 10 (meaning1035 q) (meaning1104 q) (meaning1124 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1104 = false ∨ valuation q 1124 = true := counterClause1706 (baseVal q)

theorem counterClause1707 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1118)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 5 3 (meaning1036 q) (meaning1097 q) (meaning1118 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1097 = false ∨ valuation q 1118 = true := counterClause1707 (baseVal q)

theorem counterClause1708 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1119)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 5 4 (meaning1036 q) (meaning1098 q) (meaning1119 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1098 = false ∨ valuation q 1119 = true := counterClause1708 (baseVal q)

theorem counterClause1709 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1120)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 5 5 (meaning1036 q) (meaning1099 q) (meaning1120 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1099 = false ∨ valuation q 1120 = true := counterClause1709 (baseVal q)

theorem counterClause1710 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1121)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 5 6 (meaning1036 q) (meaning1100 q) (meaning1121 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1100 = false ∨ valuation q 1121 = true := counterClause1710 (baseVal q)

theorem counterClause1711 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1096)) (literal (valuationOf q) (1118)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 6 2 (meaning1037 q) (meaning1096 q) (meaning1118 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1096 = false ∨ valuation q 1118 = true := counterClause1711 (baseVal q)

theorem counterClause1712 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1119)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 6 3 (meaning1037 q) (meaning1097 q) (meaning1119 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1097 = false ∨ valuation q 1119 = true := counterClause1712 (baseVal q)

theorem counterClause1713 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1120)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 6 4 (meaning1037 q) (meaning1098 q) (meaning1120 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1098 = false ∨ valuation q 1120 = true := counterClause1713 (baseVal q)

theorem counterClause1714 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1121)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 6 5 (meaning1037 q) (meaning1099 q) (meaning1121 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1099 = false ∨ valuation q 1121 = true := counterClause1714 (baseVal q)

theorem counterClause1715 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1122)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 6 6 (meaning1037 q) (meaning1100 q) (meaning1122 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1100 = false ∨ valuation q 1122 = true := counterClause1715 (baseVal q)

theorem counterClause1716 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1123)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 6 7 (meaning1037 q) (meaning1101 q) (meaning1123 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1101 = false ∨ valuation q 1123 = true := counterClause1716 (baseVal q)

theorem counterClause1717 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1118 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1095)) (literal (valuationOf q) (1118)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 7 1 (meaning1038 q) (meaning1095 q) (meaning1118 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1095 = false ∨ valuationOf q 1118 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1095 = false ∨ valuation q 1118 = true := counterClause1717 (baseVal q)

theorem counterClause1718 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1120)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 7 3 (meaning1038 q) (meaning1097 q) (meaning1120 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1097 = false ∨ valuation q 1120 = true := counterClause1718 (baseVal q)

theorem counterClause1719 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1121)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 7 4 (meaning1038 q) (meaning1098 q) (meaning1121 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1098 = false ∨ valuation q 1121 = true := counterClause1719 (baseVal q)

theorem counterClause1720 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1122)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 7 5 (meaning1038 q) (meaning1099 q) (meaning1122 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1099 = false ∨ valuation q 1122 = true := counterClause1720 (baseVal q)

theorem counterClause1721 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1123)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 7 6 (meaning1038 q) (meaning1100 q) (meaning1123 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1100 = false ∨ valuation q 1123 = true := counterClause1721 (baseVal q)

theorem counterClause1722 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1124)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 7 7 (meaning1038 q) (meaning1101 q) (meaning1124 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1101 = false ∨ valuation q 1124 = true := counterClause1722 (baseVal q)

theorem counterClause1723 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1096)) (literal (valuationOf q) (1120)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 8 2 (meaning1039 q) (meaning1096 q) (meaning1120 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1096 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1096 = false ∨ valuation q 1120 = true := counterClause1723 (baseVal q)

theorem counterClause1724 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1121)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 8 3 (meaning1039 q) (meaning1097 q) (meaning1121 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1097 = false ∨ valuation q 1121 = true := counterClause1724 (baseVal q)

theorem counterClause1725 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1122)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 8 4 (meaning1039 q) (meaning1098 q) (meaning1122 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1098 = false ∨ valuation q 1122 = true := counterClause1725 (baseVal q)

theorem counterClause1726 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1123)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 8 5 (meaning1039 q) (meaning1099 q) (meaning1123 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1099 = false ∨ valuation q 1123 = true := counterClause1726 (baseVal q)

theorem counterClause1727 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1123)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 9 4 (meaning1040 q) (meaning1098 q) (meaning1123 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1098 = false ∨ valuation q 1123 = true := counterClause1727 (baseVal q)

theorem counterClause1728 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) + (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (l₂ := [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1124)) (countLit q [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]) (countLit q [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]) (count1111 q) 9 5 (meaning1040 q) (meaning1099 q) (meaning1124 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1099 = false ∨ valuation q 1124 = true := counterClause1728 (baseVal q)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E256.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112256
