import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1268)) (countLit q [-15]) (countLit q [-18]) (count1268 q) 1 (meaningNeg18 q) (meaning1268 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1268 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1268)) (countLit q [-15]) (countLit q [-18]) (count1268 q) 1 (meaningNeg15 q) (meaning1268 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1268 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1270)) (countLit q [-13]) (countLit q [-15, -18]) (count1270 q) 1 (meaning1268 q) (meaning1270 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1270 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-13]) + (countLit q [-15, -18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15, -18])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1270)) (countLit q [-13]) (countLit q [-15, -18]) (count1270 q) 1 (meaningNeg13 q) (meaning1270 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1270 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1273 = true := by
  have hs : count1273 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1273)) (countLit q [-20]) (countLit q [-21]) (count1273 q) 1 (meaningNeg20 q) (meaning1273 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1273 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1275)) (countLit q [-23]) (countLit q [-26]) (count1275 q) 1 (meaningNeg26 q) (meaning1275 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1275 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1275 = true := by
  have hs : count1275 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1275)) (countLit q [-23]) (countLit q [-26]) (count1275 q) 1 (meaningNeg23 q) (meaning1275 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1275 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1275 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 1275 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-20, -21]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-23, -26])
  have hm := merge_right (literal (valuationOf q) (1275)) (literal (valuationOf q) (1277)) (countLit q [-20, -21]) (countLit q [-23, -26]) (count1277 q) 1 (meaning1275 q) (meaning1277 q) hs
  change valuationOf q 1275 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 1275 = false ∨ valuation q 1277 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1277 = true := by
  have hs : count1277 q = (countLit q [-20, -21]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-23, -26])
  have hm := merge_left (literal (valuationOf q) (1273)) (literal (valuationOf q) (1277)) (countLit q [-20, -21]) (countLit q [-23, -26]) (count1277 q) 1 (meaning1273 q) (meaning1277 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1277 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 1277 = false ∨ valuationOf q 1281 = true := by
  have hs : count1281 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -23, -26])
  have hm := merge_right (literal (valuationOf q) (1277)) (literal (valuationOf q) (1281)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -23, -26]) (count1281 q) 1 (meaning1277 q) (meaning1281 q) hs
  change valuationOf q 1277 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 1277 = false ∨ valuation q 1281 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1282 = true := by
  have hs : count1281 q = (countLit q [-13, -15, -18]) + (countLit q [-20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-13, -15, -18]) (l₂ := [-20, -21, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1270)) (literal (valuationOf q) (1277)) (literal (valuationOf q) (1282)) (countLit q [-13, -15, -18]) (countLit q [-20, -21, -23, -26]) (count1281 q) 1 1 (meaning1270 q) (meaning1277 q) (meaning1282 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1277 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1277 = false ∨ valuation q 1282 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1289 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1289)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -23, -26]) (count1288 q) 1 1 (meaning1262 q) (meaning1281 q) (meaning1289 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1281 = false ∨ valuation q 1289 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1290)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -23, -26]) (count1288 q) 1 2 (meaning1262 q) (meaning1282 q) (meaning1290 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1282 = false ∨ valuation q 1290 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1290 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1290)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -23, -26]) (count1288 q) 2 1 (meaning1263 q) (meaning1281 q) (meaning1290 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1281 = false ∨ valuation q 1290 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1263)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1291)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -23, -26]) (count1288 q) 2 2 (meaning1263 q) (meaning1282 q) (meaning1291 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1282 = false ∨ valuation q 1291 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 1264 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1291 = true := by
  have hs : count1288 q = (countLit q [-2, -4, -5, -7, -10, -12]) + (countLit q [-13, -15, -18, -20, -21, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -7, -10, -12]) (l₂ := [-13, -15, -18, -20, -21, -23, -26])
  have hm := merge_two (literal (valuationOf q) (1264)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1291)) (countLit q [-2, -4, -5, -7, -10, -12]) (countLit q [-13, -15, -18, -20, -21, -23, -26]) (count1288 q) 3 1 (meaning1264 q) (meaning1281 q) (meaning1291 q) hs
  change valuationOf q 1264 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 1264 = false ∨ valuation q 1281 = false ∨ valuation q 1291 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1301 = true := by
  have hs : count1301 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1301)) (countLit q [-29]) (countLit q [-31]) (count1301 q) 1 (meaningNeg29 q) (meaning1301 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1301 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 1301 = false ∨ valuationOf q 1303 = true := by
  have hs : count1303 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1301)) (literal (valuationOf q) (1303)) (countLit q [-28]) (countLit q [-29, -31]) (count1303 q) 1 (meaning1301 q) (meaning1303 q) hs
  change valuationOf q 1301 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 1301 = false ∨ valuation q 1303 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1306)) (countLit q [-35]) (countLit q [-37]) (count1306 q) 1 (meaningNeg35 q) (meaning1306 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1306 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (1308)) (countLit q [-33]) (countLit q [-35, -37]) (count1308 q) 1 (meaningNeg33 q) (meaning1308 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1308 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-33]) + (countLit q [-35, -37]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-35, -37])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1309)) (countLit q [-33]) (countLit q [-35, -37]) (count1308 q) 1 1 (meaningNeg33 q) (meaning1306 q) (meaning1309 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1306 = false ∨ valuation q 1309 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 1308 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -35, -37])
  have hm := merge_right (literal (valuationOf q) (1308)) (literal (valuationOf q) (1311)) (countLit q [-28, -29, -31]) (countLit q [-33, -35, -37]) (count1311 q) 1 (meaning1308 q) (meaning1311 q) hs
  change valuationOf q 1308 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 1308 = false ∨ valuation q 1311 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1308)) (literal (valuationOf q) (1312)) (countLit q [-28, -29, -31]) (countLit q [-33, -35, -37]) (count1311 q) 1 1 (meaning1303 q) (meaning1308 q) (meaning1312 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1308 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1308 = false ∨ valuation q 1312 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 1303 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1313 = true := by
  have hs : count1311 q = (countLit q [-28, -29, -31]) + (countLit q [-33, -35, -37]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-33, -35, -37])
  have hm := merge_two (literal (valuationOf q) (1303)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1313)) (countLit q [-28, -29, -31]) (countLit q [-33, -35, -37]) (count1311 q) 1 2 (meaning1303 q) (meaning1309 q) (meaning1313 q) hs
  change valuationOf q 1303 = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 1303 = false ∨ valuation q 1309 = false ∨ valuation q 1313 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1317)) (countLit q [-42]) (countLit q [-44]) (count1317 q) 1 (meaningNeg44 q) (meaning1317 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1317 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1317 = true := by
  have hs : count1317 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1317)) (countLit q [-42]) (countLit q [-44]) (count1317 q) 1 (meaningNeg42 q) (meaning1317 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1317 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1319)) (countLit q [-40]) (countLit q [-42, -44]) (count1319 q) 1 (meaning1317 q) (meaning1319 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1319 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1319)) (countLit q [-40]) (countLit q [-42, -44]) (count1319 q) 1 (meaningNeg40 q) (meaning1319 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1319 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1322 = true := by
  have hs : count1322 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1322)) (countLit q [-46]) (countLit q [-47]) (count1322 q) 1 (meaningNeg46 q) (meaning1322 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1322 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1324)) (countLit q [-49]) (countLit q [-52]) (count1324 q) 1 (meaningNeg52 q) (meaning1324 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1324 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1324 = true := by
  have hs : count1324 q = (countLit q [-49]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1324)) (countLit q [-49]) (countLit q [-52]) (count1324 q) 1 (meaningNeg49 q) (meaning1324 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1324 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1324 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 1324 = false ∨ valuationOf q 1326 = true := by
  have hs : count1326 q = (countLit q [-46, -47]) + (countLit q [-49, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-49, -52])
  have hm := merge_right (literal (valuationOf q) (1324)) (literal (valuationOf q) (1326)) (countLit q [-46, -47]) (countLit q [-49, -52]) (count1326 q) 1 (meaning1324 q) (meaning1326 q) hs
  change valuationOf q 1324 = false ∨ valuationOf q 1326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 1324 = false ∨ valuation q 1326 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E246.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112246
