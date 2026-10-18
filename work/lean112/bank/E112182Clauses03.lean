import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause97 (q : Nat → Bool) : valuationOf q 1223 = false ∨ valuationOf q 1231 = true := by
  have hs : count1231 q = (countLit q [-5, -6, -7]) + (countLit q [-9, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7]) (l₂ := [-9, -11, -14])
  have hm := merge_left (literal (valuationOf q) (1223)) (literal (valuationOf q) (1231)) (countLit q [-5, -6, -7]) (countLit q [-9, -11, -14]) (count1231 q) 1 (meaning1223 q) (meaning1231 q) hs
  change valuationOf q 1223 = false ∨ valuationOf q 1231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 1223 = false ∨ valuation q 1231 = true := counterClause97 (baseVal q)

theorem counterClause98 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1237 = true := by
  have hs : count1237 q = (countLit q [-19]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1237)) (countLit q [-19]) (countLit q [-20]) (count1237 q) 1 (meaningNeg20 q) (meaning1237 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1237 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1237 = true := counterClause98 (baseVal q)

theorem counterClause99 (q : Nat → Bool) : valuationOf q 1237 = false ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -20])
  have hm := merge_right (literal (valuationOf q) (1237)) (literal (valuationOf q) (1239)) (countLit q [-17]) (countLit q [-19, -20]) (count1239 q) 1 (meaning1237 q) (meaning1239 q) hs
  change valuationOf q 1237 = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 1237 = false ∨ valuation q 1239 = true := counterClause99 (baseVal q)

theorem counterClause100 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -20])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1239)) (countLit q [-17]) (countLit q [-19, -20]) (count1239 q) 1 (meaningNeg17 q) (meaning1239 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1239 = true := counterClause100 (baseVal q)

theorem counterClause101 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1237 = false ∨ valuationOf q 1240 = true := by
  have hs : count1239 q = (countLit q [-17]) + (countLit q [-19, -20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -20])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1237)) (literal (valuationOf q) (1240)) (countLit q [-17]) (countLit q [-19, -20]) (count1239 q) 1 1 (meaningNeg17 q) (meaning1237 q) (meaning1240 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1237 = false ∨ valuationOf q 1240 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1237 = false ∨ valuation q 1240 = true := counterClause101 (baseVal q)

theorem counterClause102 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1242)) (countLit q [-26]) (countLit q [-27]) (count1242 q) 1 (meaningNeg27 q) (meaning1242 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1242 = true := counterClause102 (baseVal q)

theorem counterClause103 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1242 = true := by
  have hs : count1242 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1242)) (countLit q [-26]) (countLit q [-27]) (count1242 q) 1 (meaningNeg26 q) (meaning1242 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1242 = true := counterClause103 (baseVal q)

theorem counterClause104 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1244 = true := by
  have hs : count1244 q = (countLit q [-22]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-26, -27])
  have hm := merge_right (literal (valuationOf q) (1242)) (literal (valuationOf q) (1244)) (countLit q [-22]) (countLit q [-26, -27]) (count1244 q) 1 (meaning1242 q) (meaning1244 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1244 = true := counterClause104 (baseVal q)

theorem counterClause105 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1244 = true := by
  have hs : count1244 q = (countLit q [-22]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-26, -27])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (1244)) (countLit q [-22]) (countLit q [-26, -27]) (count1244 q) 1 (meaningNeg22 q) (meaning1244 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1244 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1242 = false ∨ valuationOf q 1245 = true := by
  have hs : count1244 q = (countLit q [-22]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-26, -27])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (1242)) (literal (valuationOf q) (1245)) (countLit q [-22]) (countLit q [-26, -27]) (count1244 q) 1 1 (meaningNeg22 q) (meaning1242 q) (meaning1245 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1242 = false ∨ valuation q 1245 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-17, -19, -20]) + (countLit q [-22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -20]) (l₂ := [-22, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1244)) (literal (valuationOf q) (1247)) (countLit q [-17, -19, -20]) (countLit q [-22, -26, -27]) (count1247 q) 1 (meaning1244 q) (meaning1247 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1247 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1248 = true := by
  have hs : count1247 q = (countLit q [-17, -19, -20]) + (countLit q [-22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -20]) (l₂ := [-22, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1245)) (literal (valuationOf q) (1248)) (countLit q [-17, -19, -20]) (countLit q [-22, -26, -27]) (count1247 q) 2 (meaning1245 q) (meaning1248 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1248 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 1239 = false ∨ valuationOf q 1247 = true := by
  have hs : count1247 q = (countLit q [-17, -19, -20]) + (countLit q [-22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -20]) (l₂ := [-22, -26, -27])
  have hm := merge_left (literal (valuationOf q) (1239)) (literal (valuationOf q) (1247)) (countLit q [-17, -19, -20]) (countLit q [-22, -26, -27]) (count1247 q) 1 (meaning1239 q) (meaning1247 q) hs
  change valuationOf q 1239 = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 1239 = false ∨ valuation q 1247 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 1239 = false ∨ valuationOf q 1244 = false ∨ valuationOf q 1248 = true := by
  have hs : count1247 q = (countLit q [-17, -19, -20]) + (countLit q [-22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -20]) (l₂ := [-22, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1239)) (literal (valuationOf q) (1244)) (literal (valuationOf q) (1248)) (countLit q [-17, -19, -20]) (countLit q [-22, -26, -27]) (count1247 q) 1 1 (meaning1239 q) (meaning1244 q) (meaning1248 q) hs
  change valuationOf q 1239 = false ∨ valuationOf q 1244 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 1239 = false ∨ valuation q 1244 = false ∨ valuation q 1248 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 1240 = false ∨ valuationOf q 1248 = true := by
  have hs : count1247 q = (countLit q [-17, -19, -20]) + (countLit q [-22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -20]) (l₂ := [-22, -26, -27])
  have hm := merge_left (literal (valuationOf q) (1240)) (literal (valuationOf q) (1248)) (countLit q [-17, -19, -20]) (countLit q [-22, -26, -27]) (count1247 q) 2 (meaning1240 q) (meaning1248 q) hs
  change valuationOf q 1240 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 1240 = false ∨ valuation q 1248 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1253 = true := by
  have hs : count1253 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -19, -20, -22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -19, -20, -22, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1253)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -19, -20, -22, -26, -27]) (count1253 q) 1 (meaning1247 q) (meaning1253 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1253 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1254 = true := by
  have hs : count1253 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -19, -20, -22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -19, -20, -22, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1248)) (literal (valuationOf q) (1254)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -19, -20, -22, -26, -27]) (count1253 q) 2 (meaning1248 q) (meaning1254 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1254 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1253 = true := by
  have hs : count1253 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -19, -20, -22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -19, -20, -22, -26, -27])
  have hm := merge_left (literal (valuationOf q) (1231)) (literal (valuationOf q) (1253)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -19, -20, -22, -26, -27]) (count1253 q) 1 (meaning1231 q) (meaning1253 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1253 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 1231 = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1254 = true := by
  have hs : count1253 q = (countLit q [-5, -6, -7, -9, -11, -14]) + (countLit q [-17, -19, -20, -22, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14]) (l₂ := [-17, -19, -20, -22, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1231)) (literal (valuationOf q) (1247)) (literal (valuationOf q) (1254)) (countLit q [-5, -6, -7, -9, -11, -14]) (countLit q [-17, -19, -20, -22, -26, -27]) (count1253 q) 1 1 (meaning1231 q) (meaning1247 q) (meaning1254 q) hs
  change valuationOf q 1231 = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 1231 = false ∨ valuation q 1247 = false ∨ valuation q 1254 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-29]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1261)) (countLit q [-29]) (countLit q [-36]) (count1261 q) 1 (meaningNeg36 q) (meaning1261 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1261 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1261 = true := by
  have hs : count1261 q = (countLit q [-29]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (1261)) (countLit q [-29]) (countLit q [-36]) (count1261 q) 1 (meaningNeg29 q) (meaning1261 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1261 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1261 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1262 = true := by
  have hs : count1261 q = (countLit q [-29]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1262)) (countLit q [-29]) (countLit q [-36]) (count1261 q) 1 1 (meaningNeg29 q) (meaningNeg36 q) (meaning1262 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 36 = true ∨ valuation q 1262 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 1261 = false ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-28]) + (countLit q [-29, -36]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -36])
  have hm := merge_right (literal (valuationOf q) (1261)) (literal (valuationOf q) (1263)) (countLit q [-28]) (countLit q [-29, -36]) (count1263 q) 1 (meaning1261 q) (meaning1263 q) hs
  change valuationOf q 1261 = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 1261 = false ∨ valuation q 1263 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-28]) + (countLit q [-29, -36]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -36])
  have hm := merge_right (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (countLit q [-28]) (countLit q [-29, -36]) (count1263 q) 2 (meaning1262 q) (meaning1264 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1263 = true := by
  have hs : count1263 q = (countLit q [-28]) + (countLit q [-29, -36]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -36])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1263)) (countLit q [-28]) (countLit q [-29, -36]) (count1263 q) 1 (meaningNeg28 q) (meaning1263 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1263 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1261 = false ∨ valuationOf q 1264 = true := by
  have hs : count1263 q = (countLit q [-28]) + (countLit q [-29, -36]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -36])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (1261)) (literal (valuationOf q) (1264)) (countLit q [-28]) (countLit q [-29, -36]) (count1263 q) 1 1 (meaningNeg28 q) (meaning1261 q) (meaning1264 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1261 = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1261 = false ∨ valuation q 1264 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1266)) (countLit q [-38]) (countLit q [-40]) (count1266 q) 1 (meaningNeg40 q) (meaning1266 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1266 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1266 = true := by
  have hs : count1266 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1266)) (countLit q [-38]) (countLit q [-40]) (count1266 q) 1 (meaningNeg38 q) (meaning1266 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1266 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1266 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 1266 = false ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1266)) (literal (valuationOf q) (1268)) (countLit q [-37]) (countLit q [-38, -40]) (count1268 q) 1 (meaning1266 q) (meaning1268 q) hs
  change valuationOf q 1266 = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 1266 = false ∨ valuation q 1268 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1268 = true := by
  have hs : count1268 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (1268)) (countLit q [-37]) (countLit q [-38, -40]) (count1268 q) 1 (meaningNeg37 q) (meaning1268 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1268 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1268 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1266 = false ∨ valuationOf q 1269 = true := by
  have hs : count1268 q = (countLit q [-37]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (1266)) (literal (valuationOf q) (1269)) (countLit q [-37]) (countLit q [-38, -40]) (count1268 q) 1 1 (meaningNeg37 q) (meaning1266 q) (meaning1269 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1266 = false ∨ valuationOf q 1269 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1266 = false ∨ valuation q 1269 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 1268 = false ∨ valuationOf q 1271 = true := by
  have hs : count1271 q = (countLit q [-28, -29, -36]) + (countLit q [-37, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36]) (l₂ := [-37, -38, -40])
  have hm := merge_right (literal (valuationOf q) (1268)) (literal (valuationOf q) (1271)) (countLit q [-28, -29, -36]) (countLit q [-37, -38, -40]) (count1271 q) 1 (meaning1268 q) (meaning1271 q) hs
  change valuationOf q 1268 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 1268 = false ∨ valuation q 1271 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E182.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112182
