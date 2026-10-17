import E112098Semantics
import B112E098Inputs
namespace Snake9.Regrowth.E112098
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause129 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_left (literal (valuationOf q) (1222)) (literal (valuationOf q) (1248)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 1 (meaning1222 q) (meaning1248 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1248 = true := counterClause129 (baseVal q)

theorem counterClause130 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1222)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1249)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 1 1 (meaning1222 q) (meaning1241 q) (meaning1249 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1241 = false ∨ valuation q 1249 = true := counterClause130 (baseVal q)

theorem counterClause131 (q : Nat → Bool) : valuationOf q 1222 = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1250 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1222)) (literal (valuationOf q) (1242)) (literal (valuationOf q) (1250)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 1 2 (meaning1222 q) (meaning1242 q) (meaning1250 q) hs
  change valuationOf q 1222 = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 1222 = false ∨ valuation q 1242 = false ∨ valuation q 1250 = true := counterClause131 (baseVal q)

theorem counterClause132 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_left (literal (valuationOf q) (1223)) (literal (valuationOf q) (1249)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 2 (meaning1223 q) (meaning1249 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1249 = true := counterClause132 (baseVal q)

theorem counterClause133 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1250 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1223)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1250)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 2 1 (meaning1223 q) (meaning1241 q) (meaning1250 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1241 = false ∨ valuation q 1250 = true := counterClause133 (baseVal q)

theorem counterClause134 (q : Nat → Bool) : valuationOf q 1224 = false ∨ valuationOf q 1250 = true := by
  have hs : count1248 q = (countLit q [-24, -26, -29, -30, -34, -35]) + (countLit q [-37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-24, -26, -29, -30, -34, -35]) (l₂ := [-37, -38, -40, -42, -45, -46, -48])
  have hm := merge_left (literal (valuationOf q) (1224)) (literal (valuationOf q) (1250)) (countLit q [-24, -26, -29, -30, -34, -35]) (countLit q [-37, -38, -40, -42, -45, -46, -48]) (count1248 q) 3 (meaning1224 q) (meaning1250 q) hs
  change valuationOf q 1224 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 1224 = false ∨ valuation q 1250 = true := counterClause134 (baseVal q)

theorem counterClause135 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1262 = true := by
  have hs : count1259 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) + (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (l₂ := [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1262)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (count1259 q) 2 2 (meaning1202 q) (meaning1249 q) (meaning1262 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1249 = false ∨ valuation q 1262 = true := counterClause135 (baseVal q)

theorem counterClause136 (q : Nat → Bool) : valuationOf q 1202 = false ∨ valuationOf q 1250 = false ∨ valuationOf q 1263 = true := by
  have hs : count1259 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) + (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (l₂ := [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1202)) (literal (valuationOf q) (1250)) (literal (valuationOf q) (1263)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (count1259 q) 2 3 (meaning1202 q) (meaning1250 q) (meaning1263 q) hs
  change valuationOf q 1202 = false ∨ valuationOf q 1250 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 1202 = false ∨ valuation q 1250 = false ∨ valuation q 1263 = true := counterClause136 (baseVal q)

theorem counterClause137 (q : Nat → Bool) : valuationOf q 1203 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1262 = true := by
  have hs : count1259 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) + (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (l₂ := [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1203)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1262)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (count1259 q) 3 1 (meaning1203 q) (meaning1248 q) (meaning1262 q) hs
  change valuationOf q 1203 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 1203 = false ∨ valuation q 1248 = false ∨ valuation q 1262 = true := counterClause137 (baseVal q)

theorem counterClause138 (q : Nat → Bool) : valuationOf q 1203 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1263 = true := by
  have hs : count1259 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) + (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (l₂ := [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1203)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1263)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (count1259 q) 3 2 (meaning1203 q) (meaning1249 q) (meaning1263 q) hs
  change valuationOf q 1203 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 1203 = false ∨ valuation q 1249 = false ∨ valuation q 1263 = true := counterClause138 (baseVal q)

theorem counterClause139 (q : Nat → Bool) : valuationOf q 1203 = false ∨ valuationOf q 1250 = false ∨ valuationOf q 1264 = true := by
  have hs : count1259 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) + (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (l₂ := [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1203)) (literal (valuationOf q) (1250)) (literal (valuationOf q) (1264)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (count1259 q) 3 3 (meaning1203 q) (meaning1250 q) (meaning1264 q) hs
  change valuationOf q 1203 = false ∨ valuationOf q 1250 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 1203 = false ∨ valuation q 1250 = false ∨ valuation q 1264 = true := counterClause139 (baseVal q)

theorem counterClause140 (q : Nat → Bool) : valuationOf q 1204 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1263 = true := by
  have hs : count1259 q = (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) + (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (l₂ := [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48])
  have hm := merge_two (literal (valuationOf q) (1204)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1263)) (countLit q [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]) (countLit q [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]) (count1259 q) 4 1 (meaning1204 q) (meaning1248 q) (meaning1263 q) hs
  change valuationOf q 1204 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 1204 = false ∨ valuation q 1248 = false ∨ valuation q 1263 = true := counterClause140 (baseVal q)

theorem counterClause141 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1270 = true := by
  have hs : count1270 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1270)) (countLit q [-52]) (countLit q [-54]) (count1270 q) 1 (meaningNeg54 q) (meaning1270 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1270 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1270 = true := counterClause141 (baseVal q)

theorem counterClause142 (q : Nat → Bool) : valuationOf q 1270 = false ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (1270)) (literal (valuationOf q) (1272)) (countLit q [-50]) (countLit q [-52, -54]) (count1272 q) 1 (meaning1270 q) (meaning1272 q) hs
  change valuationOf q 1270 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 1270 = false ∨ valuation q 1272 = true := counterClause142 (baseVal q)

theorem counterClause143 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1272 = true := by
  have hs : count1272 q = (countLit q [-50]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52, -54])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1272)) (countLit q [-50]) (countLit q [-52, -54]) (count1272 q) 1 (meaningNeg50 q) (meaning1272 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1272 = true := counterClause143 (baseVal q)

theorem counterClause144 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1280 = true := by
  have hs : count1280 q = (countLit q [-50, -52, -54]) + (countLit q [-57, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54]) (l₂ := [-57, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1272)) (literal (valuationOf q) (1280)) (countLit q [-50, -52, -54]) (countLit q [-57, -58, -60]) (count1280 q) 1 (meaning1272 q) (meaning1280 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1280 = true := counterClause144 (baseVal q)

theorem counterClause145 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1286 = true := by
  have hs : count1286 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1286)) (countLit q [-63]) (countLit q [-66]) (count1286 q) 1 (meaningNeg63 q) (meaning1286 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1286 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1286 = true := counterClause145 (baseVal q)

theorem counterClause146 (q : Nat → Bool) : valuationOf q 1286 = false ∨ valuationOf q 1288 = true := by
  have hs : count1288 q = (countLit q [-61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1286)) (literal (valuationOf q) (1288)) (countLit q [-61]) (countLit q [-63, -66]) (count1288 q) 1 (meaning1286 q) (meaning1288 q) hs
  change valuationOf q 1286 = false ∨ valuationOf q 1288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 1286 = false ∨ valuation q 1288 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1291 = true := by
  have hs : count1291 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1291)) (countLit q [-67]) (countLit q [-70]) (count1291 q) 1 (meaningNeg70 q) (meaning1291 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1291 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1291 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1293)) (countLit q [-71]) (countLit q [-73]) (count1293 q) 1 (meaningNeg73 q) (meaning1293 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1293 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1293 = true := by
  have hs : count1293 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1293)) (countLit q [-71]) (countLit q [-73]) (count1293 q) 1 (meaningNeg71 q) (meaning1293 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1293 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1293 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1294)) (countLit q [-71]) (countLit q [-73]) (count1293 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning1294 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 1294 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 1293 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1293)) (literal (valuationOf q) (1295)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1295 q) 1 (meaning1293 q) (meaning1295 q) hs
  change valuationOf q 1293 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 1293 = false ∨ valuation q 1295 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1294)) (literal (valuationOf q) (1296)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1295 q) 2 (meaning1294 q) (meaning1296 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1296 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1295 = true := by
  have hs : count1295 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1291)) (literal (valuationOf q) (1295)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1295 q) 1 (meaning1291 q) (meaning1295 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1295 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 1291 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1296 = true := by
  have hs : count1295 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1291)) (literal (valuationOf q) (1293)) (literal (valuationOf q) (1296)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1295 q) 1 1 (meaning1291 q) (meaning1293 q) (meaning1296 q) hs
  change valuationOf q 1291 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 1291 = false ∨ valuation q 1293 = false ∨ valuation q 1296 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1299 = true := by
  have hs : count1299 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1295)) (literal (valuationOf q) (1299)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -71, -73]) (count1299 q) 1 (meaning1295 q) (meaning1299 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1299 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1300)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -71, -73]) (count1299 q) 2 (meaning1296 q) (meaning1300 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1300 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1300 = true := by
  have hs : count1299 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1300)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -71, -73]) (count1299 q) 1 1 (meaning1288 q) (meaning1295 q) (meaning1300 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1295 = false ∨ valuation q 1300 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 1288 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1301 = true := by
  have hs : count1299 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1288)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1301)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -71, -73]) (count1299 q) 1 2 (meaning1288 q) (meaning1296 q) (meaning1301 q) hs
  change valuationOf q 1288 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 1288 = false ∨ valuation q 1296 = false ∨ valuation q 1301 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1307 = true := by
  have hs : count1306 q = (countLit q [-50, -52, -54, -57, -58, -60]) + (countLit q [-61, -63, -66, -67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60]) (l₂ := [-61, -63, -66, -67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1299)) (literal (valuationOf q) (1307)) (countLit q [-50, -52, -54, -57, -58, -60]) (countLit q [-61, -63, -66, -67, -70, -71, -73]) (count1306 q) 1 1 (meaning1280 q) (meaning1299 q) (meaning1307 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1299 = false ∨ valuationOf q 1307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1299 = false ∨ valuation q 1307 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 1280 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1308 = true := by
  have hs : count1306 q = (countLit q [-50, -52, -54, -57, -58, -60]) + (countLit q [-61, -63, -66, -67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-50, -52, -54, -57, -58, -60]) (l₂ := [-61, -63, -66, -67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1280)) (literal (valuationOf q) (1300)) (literal (valuationOf q) (1308)) (countLit q [-50, -52, -54, -57, -58, -60]) (countLit q [-61, -63, -66, -67, -70, -71, -73]) (count1306 q) 1 2 (meaning1280 q) (meaning1300 q) (meaning1308 q) hs
  change valuationOf q 1280 = false ∨ valuationOf q 1300 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 1280 = false ∨ valuation q 1300 = false ∨ valuation q 1308 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E098.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112098
