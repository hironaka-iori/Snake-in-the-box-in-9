import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1013 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (999)) (literal (valuationOf q) (1005)) (literal (valuationOf q) (1013)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 4 2 (meaning999 q) (meaning1005 q) (meaning1013 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1005 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1005 = false ∨ valuation q 1013 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1014 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (999)) (literal (valuationOf q) (1006)) (literal (valuationOf q) (1014)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 4 3 (meaning999 q) (meaning1006 q) (meaning1014 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1006 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1006 = false ∨ valuation q 1014 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 999 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1015 = true := by
  have hs : count1008 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (999)) (literal (valuationOf q) (1007)) (literal (valuationOf q) (1015)) (countLit q [-76, -79, -81, -82]) (countLit q [-86, -87, -89, -91]) (count1008 q) 4 4 (meaning999 q) (meaning1007 q) (meaning1015 q) hs
  change valuationOf q 999 = false ∨ valuationOf q 1007 = false ∨ valuationOf q 1015 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 999 = false ∨ valuation q 1007 = false ∨ valuation q 1015 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1008)) (literal (valuationOf q) (1016)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 (meaning1008 q) (meaning1016 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1016 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1009)) (literal (valuationOf q) (1017)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 (meaning1009 q) (meaning1017 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1017 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1010 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1010)) (literal (valuationOf q) (1018)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 (meaning1010 q) (meaning1018 q) hs
  change valuationOf q 1010 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1010 = false ∨ valuation q 1018 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1011 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1011)) (literal (valuationOf q) (1019)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 4 (meaning1011 q) (meaning1019 q) hs
  change valuationOf q 1011 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1011 = false ∨ valuation q 1019 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1012)) (literal (valuationOf q) (1020)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 5 (meaning1012 q) (meaning1020 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1020 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1013)) (literal (valuationOf q) (1021)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 6 (meaning1013 q) (meaning1021 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1021 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1014)) (literal (valuationOf q) (1022)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 7 (meaning1014 q) (meaning1022 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1022 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1023 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1015)) (literal (valuationOf q) (1023)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 8 (meaning1015 q) (meaning1023 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1023 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (985)) (literal (valuationOf q) (1016)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 (meaning985 q) (meaning1016 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1016 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1017)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 1 (meaning985 q) (meaning1008 q) (meaning1017 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1008 = false ∨ valuation q 1017 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1018)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 2 (meaning985 q) (meaning1009 q) (meaning1018 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1009 = false ∨ valuation q 1018 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1019)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 3 (meaning985 q) (meaning1010 q) (meaning1019 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1010 = false ∨ valuation q 1019 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1020)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 4 (meaning985 q) (meaning1011 q) (meaning1020 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1011 = false ∨ valuation q 1020 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 5 (meaning985 q) (meaning1012 q) (meaning1021 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1012 = false ∨ valuation q 1021 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1013 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1013)) (literal (valuationOf q) (1022)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 6 (meaning985 q) (meaning1013 q) (meaning1022 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1013 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1013 = false ∨ valuation q 1022 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 985 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1023 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (985)) (literal (valuationOf q) (1014)) (literal (valuationOf q) (1023)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 1 7 (meaning985 q) (meaning1014 q) (meaning1023 q) hs
  change valuationOf q 985 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 985 = false ∨ valuation q 1014 = false ∨ valuation q 1023 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (986)) (literal (valuationOf q) (1017)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 (meaning986 q) (meaning1017 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1017 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1018)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 1 (meaning986 q) (meaning1008 q) (meaning1018 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1008 = false ∨ valuation q 1018 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1019)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 2 (meaning986 q) (meaning1009 q) (meaning1019 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1009 = false ∨ valuation q 1019 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1020)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 3 (meaning986 q) (meaning1010 q) (meaning1020 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1010 = false ∨ valuation q 1020 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1021)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 4 (meaning986 q) (meaning1011 q) (meaning1021 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1011 = false ∨ valuation q 1021 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1012)) (literal (valuationOf q) (1022)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 5 (meaning986 q) (meaning1012 q) (meaning1022 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1012 = false ∨ valuation q 1022 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 986 = false ∨ valuationOf q 1013 = false ∨ valuationOf q 1023 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (986)) (literal (valuationOf q) (1013)) (literal (valuationOf q) (1023)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 2 6 (meaning986 q) (meaning1013 q) (meaning1023 q) hs
  change valuationOf q 986 = false ∨ valuationOf q 1013 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 986 = false ∨ valuation q 1013 = false ∨ valuation q 1023 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (987)) (literal (valuationOf q) (1018)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 (meaning987 q) (meaning1018 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1018 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1019 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1008)) (literal (valuationOf q) (1019)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 1 (meaning987 q) (meaning1008 q) (meaning1019 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1008 = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1008 = false ∨ valuation q 1019 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1020 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1020)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 2 (meaning987 q) (meaning1009 q) (meaning1020 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1009 = false ∨ valuation q 1020 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1021 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1021)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 3 (meaning987 q) (meaning1010 q) (meaning1021 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1010 = false ∨ valuation q 1021 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1022 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1022)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 4 (meaning987 q) (meaning1011 q) (meaning1022 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1011 = false ∨ valuation q 1022 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1023 = true := by
  have hs : count1016 q = (countLit q [-61, -64, -65, -69, -70, -72, -74]) + (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74]) (l₂ := [-76, -79, -81, -82, -86, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1012)) (literal (valuationOf q) (1023)) (countLit q [-61, -64, -65, -69, -70, -72, -74]) (countLit q [-76, -79, -81, -82, -86, -87, -89, -91]) (count1016 q) 3 5 (meaning987 q) (meaning1012 q) (meaning1023 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1012 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1012 = false ∨ valuation q 1023 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E097.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112097
