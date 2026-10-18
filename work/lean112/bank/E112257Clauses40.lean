import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1039 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1039)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 2 7 (meaning959 q) (meaning1022 q) (meaning1039 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1022 = false ∨ valuation q 1039 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 959 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1040 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (959)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1040)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 2 8 (meaning959 q) (meaning1023 q) (meaning1040 q) hs
  change valuationOf q 959 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 959 = false ∨ valuation q 1023 = false ∨ valuation q 1040 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1017 = false ∨ valuationOf q 1035 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1017)) (literal (valuationOf q) (1035)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 2 (meaning960 q) (meaning1017 q) (meaning1035 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1017 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1017 = false ∨ valuation q 1035 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1036 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1036)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 3 (meaning960 q) (meaning1018 q) (meaning1036 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1018 = false ∨ valuation q 1036 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1037 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1037)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 4 (meaning960 q) (meaning1019 q) (meaning1037 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1019 = false ∨ valuation q 1037 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1038 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1038)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 5 (meaning960 q) (meaning1020 q) (meaning1038 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1020 = false ∨ valuation q 1038 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1039 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1039)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 6 (meaning960 q) (meaning1021 q) (meaning1039 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1021 = false ∨ valuation q 1039 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1040 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1040)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 7 (meaning960 q) (meaning1022 q) (meaning1040 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1022 = false ∨ valuation q 1040 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1041 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1041)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 3 8 (meaning960 q) (meaning1023 q) (meaning1041 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 1023 = false ∨ valuation q 1041 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1037 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1037)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 4 3 (meaning961 q) (meaning1018 q) (meaning1037 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1018 = false ∨ valuation q 1037 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1038 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1038)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 4 4 (meaning961 q) (meaning1019 q) (meaning1038 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1019 = false ∨ valuation q 1038 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1039 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1039)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 4 5 (meaning961 q) (meaning1020 q) (meaning1039 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1020 = false ∨ valuation q 1039 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1040 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1040)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 4 6 (meaning961 q) (meaning1021 q) (meaning1040 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1021 = false ∨ valuation q 1040 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1041 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1041)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 4 7 (meaning961 q) (meaning1022 q) (meaning1041 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1022 = false ∨ valuation q 1041 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1042 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1042)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 4 8 (meaning961 q) (meaning1023 q) (meaning1042 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 1023 = false ∨ valuation q 1042 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1038 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1038)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 5 3 (meaning962 q) (meaning1018 q) (meaning1038 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1018 = false ∨ valuation q 1038 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1039 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1039)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 5 4 (meaning962 q) (meaning1019 q) (meaning1039 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1019 = false ∨ valuation q 1039 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1040 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1040)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 5 5 (meaning962 q) (meaning1020 q) (meaning1040 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1020 = false ∨ valuation q 1040 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1041 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1041)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 5 6 (meaning962 q) (meaning1021 q) (meaning1041 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1021 = false ∨ valuation q 1041 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1042 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1042)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 5 7 (meaning962 q) (meaning1022 q) (meaning1042 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1022 = false ∨ valuation q 1042 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1043 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1043)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 5 8 (meaning962 q) (meaning1023 q) (meaning1043 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 1023 = false ∨ valuation q 1043 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1039 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1039)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 6 3 (meaning963 q) (meaning1018 q) (meaning1039 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 1018 = false ∨ valuation q 1039 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1040 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1040)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 6 4 (meaning963 q) (meaning1019 q) (meaning1040 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 1019 = false ∨ valuation q 1040 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1041 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1041)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 6 5 (meaning963 q) (meaning1020 q) (meaning1041 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 1020 = false ∨ valuation q 1041 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1043 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (963)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1043)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 6 7 (meaning963 q) (meaning1022 q) (meaning1043 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 1022 = false ∨ valuation q 1043 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 964 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1041 = true := by
  have hs : count1031 q = (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) + (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (l₂ := [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (964)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1041)) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87]) (countLit q [-89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1031 q) 7 4 (meaning964 q) (meaning1019 q) (meaning1041 q) hs
  change valuationOf q 964 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 964 = false ∨ valuation q 1019 = false ∨ valuation q 1041 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (904)) (literal (valuationOf q) (1043)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 5 13 (meaning904 q) (meaning1043 q) (meaning1066 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 1043 = false ∨ valuation q 1066 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (905)) (literal (valuationOf q) (1042)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 6 12 (meaning905 q) (meaning1042 q) (meaning1066 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 1042 = false ∨ valuation q 1066 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (906)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 7 11 (meaning906 q) (meaning1041 q) (meaning1066 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 1041 = false ∨ valuation q 1066 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (1040)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 8 10 (meaning907 q) (meaning1040 q) (meaning1066 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 1040 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 1040 = false ∨ valuation q 1066 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (1039)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 9 9 (meaning908 q) (meaning1039 q) (meaning1066 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 1039 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 1039 = false ∨ valuation q 1066 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1066 = true := by
  have hs : count1049 q = (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) + (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (l₂ := [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (1038)) (literal (valuationOf q) (1066)) (countLit q [-1, -2, -4, -6, -7, -11, -12, -15, -16, -19, -21, -23, -26, -28, -30, -32, -34, -40, -42, -44, -45, -46, -48, -49, -50, -52, -54, -59, -60]) (countLit q [-62, -63, -64, -66, -68, -70, -71, -72, -75, -79, -81, -82, -85, -87, -89, -91, -93, -95, -99, -101, -102, -105, -107, -108, -109, -111, -112, -113, -114]) (count1049 q) 10 8 (meaning909 q) (meaning1038 q) (meaning1066 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 1038 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 1038 = false ∨ valuation q 1066 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E257.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112257
