import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1137 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1137)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 6 7 (meaning1072 q) (meaning1137 q) (meaning1159 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1137 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1137 = false ∨ valuation q 1159 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1138 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1138)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 6 8 (meaning1072 q) (meaning1138 q) (meaning1160 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1138 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1138 = false ∨ valuation q 1160 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1156 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1073)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1156)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 7 3 (meaning1073 q) (meaning1133 q) (meaning1156 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1133 = false ∨ valuation q 1156 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1157 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1073)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1157)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 7 4 (meaning1073 q) (meaning1134 q) (meaning1157 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1134 = false ∨ valuation q 1157 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1073)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 7 5 (meaning1073 q) (meaning1135 q) (meaning1158 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1135 = false ∨ valuation q 1158 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1073)) (literal (valuationOf q) (1136)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 7 6 (meaning1073 q) (meaning1136 q) (meaning1159 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1136 = false ∨ valuation q 1159 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1137 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1073)) (literal (valuationOf q) (1137)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 7 7 (meaning1073 q) (meaning1137 q) (meaning1160 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1137 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1137 = false ∨ valuation q 1160 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1155 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1074)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1155)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 8 1 (meaning1074 q) (meaning1131 q) (meaning1155 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1131 = false ∨ valuation q 1155 = true := counterClause1800 (baseVal q)

theorem counterClause1801 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1156 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1074)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1156)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 8 2 (meaning1074 q) (meaning1132 q) (meaning1156 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1132 = false ∨ valuation q 1156 = true := counterClause1801 (baseVal q)

theorem counterClause1802 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1157 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1074)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1157)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 8 3 (meaning1074 q) (meaning1133 q) (meaning1157 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1133 = false ∨ valuation q 1157 = true := counterClause1802 (baseVal q)

theorem counterClause1803 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1074)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 8 4 (meaning1074 q) (meaning1134 q) (meaning1158 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1134 = false ∨ valuation q 1158 = true := counterClause1803 (baseVal q)

theorem counterClause1804 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1074)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 8 5 (meaning1074 q) (meaning1135 q) (meaning1159 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1135 = false ∨ valuation q 1159 = true := counterClause1804 (baseVal q)

theorem counterClause1805 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1074)) (literal (valuationOf q) (1136)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 8 6 (meaning1074 q) (meaning1136 q) (meaning1160 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1136 = false ∨ valuation q 1160 = true := counterClause1805 (baseVal q)

theorem counterClause1806 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1156 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1156)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 9 1 (meaning1075 q) (meaning1131 q) (meaning1156 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1131 = false ∨ valuation q 1156 = true := counterClause1806 (baseVal q)

theorem counterClause1807 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1157 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1157)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 9 2 (meaning1075 q) (meaning1132 q) (meaning1157 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1132 = false ∨ valuation q 1157 = true := counterClause1807 (baseVal q)

theorem counterClause1808 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 9 3 (meaning1075 q) (meaning1133 q) (meaning1158 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1133 = false ∨ valuation q 1158 = true := counterClause1808 (baseVal q)

theorem counterClause1809 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 9 4 (meaning1075 q) (meaning1134 q) (meaning1159 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1134 = false ∨ valuation q 1159 = true := counterClause1809 (baseVal q)

theorem counterClause1810 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 9 5 (meaning1075 q) (meaning1135 q) (meaning1160 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1135 = false ∨ valuation q 1160 = true := counterClause1810 (baseVal q)

theorem counterClause1811 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1161 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1136)) (literal (valuationOf q) (1161)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 9 6 (meaning1075 q) (meaning1136 q) (meaning1161 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1136 = false ∨ valuation q 1161 = true := counterClause1811 (baseVal q)

theorem counterClause1812 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1156 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1076)) (literal (valuationOf q) (1156)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 10 (meaning1076 q) (meaning1156 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1156 = true := counterClause1812 (baseVal q)

theorem counterClause1813 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1157 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1157)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 10 1 (meaning1076 q) (meaning1131 q) (meaning1157 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1131 = false ∨ valuation q 1157 = true := counterClause1813 (baseVal q)

theorem counterClause1814 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 10 2 (meaning1076 q) (meaning1132 q) (meaning1158 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1132 = false ∨ valuation q 1158 = true := counterClause1814 (baseVal q)

theorem counterClause1815 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 10 3 (meaning1076 q) (meaning1133 q) (meaning1159 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1133 = false ∨ valuation q 1159 = true := counterClause1815 (baseVal q)

theorem counterClause1816 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 10 4 (meaning1076 q) (meaning1134 q) (meaning1160 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1134 = false ∨ valuation q 1160 = true := counterClause1816 (baseVal q)

theorem counterClause1817 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1161 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1161)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 10 5 (meaning1076 q) (meaning1135 q) (meaning1161 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1135 = false ∨ valuation q 1161 = true := counterClause1817 (baseVal q)

theorem counterClause1818 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 11 1 (meaning1077 q) (meaning1131 q) (meaning1158 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1131 = false ∨ valuation q 1158 = true := counterClause1818 (baseVal q)

theorem counterClause1819 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 11 2 (meaning1077 q) (meaning1132 q) (meaning1159 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1132 = false ∨ valuation q 1159 = true := counterClause1819 (baseVal q)

theorem counterClause1820 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 11 3 (meaning1077 q) (meaning1133 q) (meaning1160 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1133 = false ∨ valuation q 1160 = true := counterClause1820 (baseVal q)

theorem counterClause1821 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1161 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1134)) (literal (valuationOf q) (1161)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 11 4 (meaning1077 q) (meaning1134 q) (meaning1161 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1134 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1134 = false ∨ valuation q 1161 = true := counterClause1821 (baseVal q)

theorem counterClause1822 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 12 1 (meaning1078 q) (meaning1131 q) (meaning1159 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1131 = false ∨ valuation q 1159 = true := counterClause1822 (baseVal q)

theorem counterClause1823 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 12 2 (meaning1078 q) (meaning1132 q) (meaning1160 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1132 = false ∨ valuation q 1160 = true := counterClause1823 (baseVal q)

theorem counterClause1824 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1161 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1161)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 12 3 (meaning1078 q) (meaning1133 q) (meaning1161 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1161 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1133 = false ∨ valuation q 1161 = true := counterClause1824 (baseVal q)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E057.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112057
