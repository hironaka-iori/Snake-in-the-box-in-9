import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1293 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1284)) (literal (valuationOf q) (1293)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 2 4 (meaning1263 q) (meaning1284 q) (meaning1293 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1284 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1284 = false ∨ valuation q 1293 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_left (literal (valuationOf q) (1264)) (literal (valuationOf q) (1290)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 3 (meaning1264 q) (meaning1290 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1290 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1291)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 3 1 (meaning1264 q) (meaning1281 q) (meaning1291 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1281 = false ∨ valuation q 1291 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1292 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1292)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 3 2 (meaning1264 q) (meaning1282 q) (meaning1292 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1282 = false ∨ valuation q 1292 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1293 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1283)) (literal (valuationOf q) (1293)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 3 3 (meaning1264 q) (meaning1283 q) (meaning1293 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1283 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1283 = false ∨ valuation q 1293 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_left (literal (valuationOf q) (1265)) (literal (valuationOf q) (1291)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 4 (meaning1265 q) (meaning1291 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1291 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1292 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1292)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 4 1 (meaning1265 q) (meaning1281 q) (meaning1292 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1281 = false ∨ valuation q 1292 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 1265 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1293 = true := by
  have hs : count1288 q = (countLit q [-1, -2, -5, -7, -9, -11]) + (countLit q [-12, -14, -17, -19, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -9, -11]) (l₂ := [-12, -14, -17, -19, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1265)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1293)) (countLit q [-1, -2, -5, -7, -9, -11]) (countLit q [-12, -14, -17, -19, -20, -23, -26]) (count1288 q) 4 2 (meaning1265 q) (meaning1282 q) (meaning1293 q) hs
  change valuationOf q 1265 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 1265 = false ∨ valuation q 1282 = false ∨ valuation q 1293 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1301)) (countLit q [-29]) (countLit q [-31]) (count1301 q) 1 (meaningNeg31 q) (meaning1301 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1301 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1301)) (literal (valuationOf q) (1303)) (countLit q [-28]) (countLit q [-29, -31]) (count1303 q) 1 (meaning1301 q) (meaning1303 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1303 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1303)) (countLit q [-28]) (countLit q [-29, -31]) (count1303 q) 1 (meaningNeg28 q) (meaning1303 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1303 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1306)) (countLit q [-35]) (countLit q [-37]) (count1306 q) 1 (meaningNeg35 q) (meaning1306 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1306 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-34]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35, -37])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-34]) (countLit q [-35, -37]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-34]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1308)) (countLit q [-34]) (countLit q [-35, -37]) (count1308 q) 1 (meaningNeg34 q) (meaning1308 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1308 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-28, -29, -31]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-34, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1311)) (countLit q [-28, -29, -31]) (countLit q [-34, -35, -37]) (count1311 q) 1 (meaning1308 q) (meaning1311 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1311 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-28, -29, -31]) + (countLit q [-34, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-34, -35, -37])
  have hm := merge_left (literal (valuationOf q) (1303)) (literal (valuationOf q) (1311)) (countLit q [-28, -29, -31]) (countLit q [-34, -35, -37]) (count1311 q) 1 (meaning1303 q) (meaning1311 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1311 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1317)) (countLit q [-43]) (countLit q [-45]) (count1317 q) 1 (meaningNeg45 q) (meaning1317 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1317 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1317)) (countLit q [-43]) (countLit q [-45]) (count1317 q) 1 (meaningNeg43 q) (meaning1317 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1317 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1319)) (countLit q [-40]) (countLit q [-43, -45]) (count1319 q) 1 (meaning1317 q) (meaning1319 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1319 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1319)) (countLit q [-40]) (countLit q [-43, -45]) (count1319 q) 1 (meaningNeg40 q) (meaning1319 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1319 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1317 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1320)) (countLit q [-40]) (countLit q [-43, -45]) (count1319 q) 1 1 (meaningNeg40 q) (meaning1317 q) (meaning1320 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1317 = false ∨ valuation q 1320 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1322)) (countLit q [-46]) (countLit q [-47]) (count1322 q) 1 (meaningNeg47 q) (meaning1322 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1322 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1322)) (countLit q [-46]) (countLit q [-47]) (count1322 q) 1 (meaningNeg46 q) (meaning1322 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1322 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1323 = true := by
  have hs : count1322 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1323)) (countLit q [-46]) (countLit q [-47]) (count1322 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning1323 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1323 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 1323 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1324)) (countLit q [-50]) (countLit q [-52]) (count1324 q) 1 (meaningNeg52 q) (meaning1324 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1324 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1324)) (countLit q [-50]) (countLit q [-52]) (count1324 q) 1 (meaningNeg50 q) (meaning1324 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1324 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-46, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -52])
  have hm := merge_right (literal (valuationOf q) (1324)) (literal (valuationOf q) (1326)) (countLit q [-46, -47]) (countLit q [-50, -52]) (count1326 q) 1 (meaning1324 q) (meaning1326 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1326 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-46, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (1322)) (literal (valuationOf q) (1326)) (countLit q [-46, -47]) (countLit q [-50, -52]) (count1326 q) 1 (meaning1322 q) (meaning1326 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1326 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 1322 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-46, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -52])
  have hm := merge_two (literal (valuationOf q) (1322)) (literal (valuationOf q) (1324)) (literal (valuationOf q) (1327)) (countLit q [-46, -47]) (countLit q [-50, -52]) (count1326 q) 1 1 (meaning1322 q) (meaning1324 q) (meaning1327 q) hs
  change valuationOf q 1322 = false ∨ valuationOf q 1324 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 1322 = false ∨ valuation q 1324 = false ∨ valuation q 1327 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 1323 = false ∨ valuationOf q 1327 = true := by
  have hs : count1326 q = (countLit q [-46, -47]) + (countLit q [-50, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -52])
  have hm := merge_left (literal (valuationOf q) (1323)) (literal (valuationOf q) (1327)) (countLit q [-46, -47]) (countLit q [-50, -52]) (count1326 q) 2 (meaning1323 q) (meaning1327 q) hs
  change valuationOf q 1323 = false ∨ valuationOf q 1327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 1323 = false ∨ valuation q 1327 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 1326 = false ∨ valuationOf q 1330 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1326)) (literal (valuationOf q) (1330)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 1 (meaning1326 q) (meaning1330 q) hs
  change valuationOf q 1326 = false ∨ valuationOf q 1330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 1326 = false ∨ valuation q 1330 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1331 = true := by
  have hs : count1330 q = (countLit q [-40, -43, -45]) + (countLit q [-46, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-40, -43, -45]) (l₂ := [-46, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1327)) (literal (valuationOf q) (1331)) (countLit q [-40, -43, -45]) (countLit q [-46, -47, -50, -52]) (count1330 q) 2 (meaning1327 q) (meaning1331 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1331 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E144.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112144
