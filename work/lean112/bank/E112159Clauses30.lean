import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1056 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1056)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 4 2 (meaning980 q) (meaning1037 q) (meaning1056 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1037 = false ∨ valuation q 1056 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1057 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1057)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 4 3 (meaning980 q) (meaning1038 q) (meaning1057 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1038 = false ∨ valuation q 1057 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1058 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1058)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 4 4 (meaning980 q) (meaning1039 q) (meaning1058 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1039 = false ∨ valuation q 1058 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1059 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1059)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 4 5 (meaning980 q) (meaning1040 q) (meaning1059 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1040 = false ∨ valuation q 1059 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1060 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (980)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1060)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 4 6 (meaning980 q) (meaning1041 q) (meaning1060 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 1041 = false ∨ valuation q 1060 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1058 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1058)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 5 3 (meaning981 q) (meaning1038 q) (meaning1058 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1038 = false ∨ valuation q 1058 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1059 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1059)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 5 4 (meaning981 q) (meaning1039 q) (meaning1059 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1039 = false ∨ valuation q 1059 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 981 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1060 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (981)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1060)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 5 5 (meaning981 q) (meaning1040 q) (meaning1060 q) hs
  change valuationOf q 981 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 981 = false ∨ valuation q 1040 = false ∨ valuation q 1060 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 982 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1059 = true := by
  have hs : count1051 q = (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) + (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (l₂ := [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (982)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1059)) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87]) (countLit q [-88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1051 q) 6 3 (meaning982 q) (meaning1038 q) (meaning1059 q) hs
  change valuationOf q 982 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 982 = false ∨ valuation q 1038 = false ∨ valuation q 1059 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 9 10 (meaning922 q) (meaning1060 q) (meaning1088 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 1060 = false ∨ valuation q 1088 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 10 9 (meaning923 q) (meaning1059 q) (meaning1088 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 1059 = false ∨ valuation q 1088 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 11 8 (meaning924 q) (meaning1058 q) (meaning1088 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 1058 = false ∨ valuation q 1088 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 12 7 (meaning925 q) (meaning1057 q) (meaning1088 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 1057 = false ∨ valuation q 1088 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 13 6 (meaning926 q) (meaning1056 q) (meaning1088 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 1056 = false ∨ valuation q 1088 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (927)) (literal (valuationOf q) (1055)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 14 5 (meaning927 q) (meaning1055 q) (meaning1088 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 1055 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 1055 = false ∨ valuation q 1088 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1088 = true := by
  have hs : count1070 q = (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) + (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (l₂ := [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1088)) (countLit q [-1, -3, -4, -5, -7, -9, -10, -12, -14, -15, -18, -21, -23, -24, -27, -29, -30, -32, -36, -37, -39, -41, -45, -46, -49, -50, -51, -54, -55]) (countLit q [-58, -60, -61, -66, -67, -68, -71, -72, -74, -78, -79, -81, -82, -84, -87, -88, -90, -94, -95, -98, -99, -101, -104, -105, -106, -108, -111, -113, -115, -117]) (count1070 q) 15 4 (meaning928 q) (meaning1054 q) (meaning1088 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 1054 = false ∨ valuation q 1088 = true := counterClause976 (baseVal q)

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1088 = false := by
  rw [value1088]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1070 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 6 = false ∨ valuation q 34 = false ∨ valuation q 41 = false := by
  rw [value4, value6, value34, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (101 : Vertex) (109 : Vertex) (229 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 40 = false ∨ valuation q 51 = false := by
  rw [value5, value8, value40, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (108 : Vertex) (124 : Vertex) (236 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value12, value13, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (162 : Vertex) (176 : Vertex) (178 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value14, value19, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (165 : Vertex) (173 : Vertex) (181 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 34 = false ∨ valuation q 41 = false := by
  rw [value14, value19, value34, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (165 : Vertex) (173 : Vertex) (229 : Vertex) (237 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 26 = false ∨ valuation q 34 = false ∨ valuation q 45 = false := by
  rw [value14, value26, value34, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (165 : Vertex) (181 : Vertex) (229 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 18 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value16, value18, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (172 : Vertex) (232 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 31 = false := by
  rw [value17, value21, value27, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (175 : Vertex) (187 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value18, value19, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (172 : Vertex) (173 : Vertex) (174 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value18, value19, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (172 : Vertex) (173 : Vertex) (188 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 30 = false := by
  rw [value18, value20, value28, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (172 : Vertex) (174 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 29 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value26, value29, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (181 : Vertex) (189 : Vertex) (437 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value28, value30, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (190 : Vertex) (252 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value32, value33, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (225 : Vertex) (227 : Vertex) (229 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E159.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112159
