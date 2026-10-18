import E112242Semantics
import B112E242Inputs
namespace Snake9.Regrowth.E112242
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause97 (q : Nat → Bool) : valuationOf q 1237 = false ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (1237)) (literal (valuationOf q) (1239)) (countLit q [-28]) (countLit q [-29, -31]) (count1239 q) 1 (meaning1237 q) (meaning1239 q) hs
  change valuationOf q 1237 = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 1237 = false ∨ valuation q 1239 = true := counterClause97 (baseVal q)

theorem counterClause98 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1239 = true := by
  have hs : count1239 q = (countLit q [-28]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1239)) (countLit q [-28]) (countLit q [-29, -31]) (count1239 q) 1 (meaningNeg28 q) (meaning1239 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1239 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1239 = true := counterClause98 (baseVal q)

theorem counterClause99 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1244 = true := by
  have hs : count1244 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1244)) (countLit q [-38]) (countLit q [-40]) (count1244 q) 1 (meaningNeg40 q) (meaning1244 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1244 = true := counterClause99 (baseVal q)

theorem counterClause100 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-34, -35]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-34, -35]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (1244)) (literal (valuationOf q) (1246)) (countLit q [-34, -35]) (countLit q [-38, -40]) (count1246 q) 1 (meaning1244 q) (meaning1246 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1246 = true := counterClause100 (baseVal q)

theorem counterClause101 (q : Nat → Bool) : valuationOf q 1239 = false ∨ valuationOf q 1246 = false ∨ valuationOf q 1251 = true := by
  have hs : count1250 q = (countLit q [-28, -29, -31]) + (countLit q [-34, -35, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31]) (l₂ := [-34, -35, -38, -40])
  have hm := merge_two (literal (valuationOf q) (1239)) (literal (valuationOf q) (1246)) (literal (valuationOf q) (1251)) (countLit q [-28, -29, -31]) (countLit q [-34, -35, -38, -40]) (count1250 q) 1 1 (meaning1239 q) (meaning1246 q) (meaning1251 q) hs
  change valuationOf q 1239 = false ∨ valuationOf q 1246 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 1239 = false ∨ valuation q 1246 = false ∨ valuation q 1251 = true := counterClause101 (baseVal q)

theorem counterClause102 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1257)) (countLit q [-42]) (countLit q [-44]) (count1257 q) 1 (meaningNeg44 q) (meaning1257 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1257 = true := counterClause102 (baseVal q)

theorem counterClause103 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1257)) (countLit q [-42]) (countLit q [-44]) (count1257 q) 1 (meaningNeg42 q) (meaning1257 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1257 = true := counterClause103 (baseVal q)

theorem counterClause104 (q : Nat → Bool) : valuationOf q 1257 = false ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1257)) (literal (valuationOf q) (1259)) (countLit q [-41]) (countLit q [-42, -44]) (count1259 q) 1 (meaning1257 q) (meaning1259 q) hs
  change valuationOf q 1257 = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 1257 = false ∨ valuation q 1259 = true := counterClause104 (baseVal q)

theorem counterClause105 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1259 = true := by
  have hs : count1259 q = (countLit q [-41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1259)) (countLit q [-41]) (countLit q [-42, -44]) (count1259 q) 1 (meaningNeg41 q) (meaning1259 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1259 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1259 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true := by
  have hs : count1259 q = (countLit q [-41]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (1257)) (literal (valuationOf q) (1260)) (countLit q [-41]) (countLit q [-42, -44]) (count1259 q) 1 1 (meaningNeg41 q) (meaning1257 q) (meaning1260 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1257 = false ∨ valuationOf q 1260 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1257 = false ∨ valuation q 1260 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1262 = true := by
  have hs : count1262 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1262)) (countLit q [-45]) (countLit q [-47]) (count1262 q) 1 (meaningNeg45 q) (meaning1262 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1262 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1262 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1263 = true := by
  have hs : count1262 q = (countLit q [-45]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1263)) (countLit q [-45]) (countLit q [-47]) (count1262 q) 1 1 (meaningNeg45 q) (meaningNeg47 q) (meaning1263 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1263 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 47 = true ∨ valuation q 1263 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1264)) (countLit q [-48]) (countLit q [-50]) (count1264 q) 1 (meaningNeg50 q) (meaning1264 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1264 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1264 = true := by
  have hs : count1264 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1264)) (countLit q [-48]) (countLit q [-50]) (count1264 q) 1 (meaningNeg48 q) (meaning1264 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1264 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1264 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 1262 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-45, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1262)) (literal (valuationOf q) (1264)) (literal (valuationOf q) (1267)) (countLit q [-45, -47]) (countLit q [-48, -50]) (count1266 q) 1 1 (meaning1262 q) (meaning1264 q) (meaning1267 q) hs
  change valuationOf q 1262 = false ∨ valuationOf q 1264 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 1262 = false ∨ valuation q 1264 = false ∨ valuation q 1267 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 1263 = false ∨ valuationOf q 1267 = true := by
  have hs : count1266 q = (countLit q [-45, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-45, -47]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (1263)) (literal (valuationOf q) (1267)) (countLit q [-45, -47]) (countLit q [-48, -50]) (count1266 q) 2 (meaning1263 q) (meaning1267 q) hs
  change valuationOf q 1263 = false ∨ valuationOf q 1267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 1263 = false ∨ valuation q 1267 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 1267 = false ∨ valuationOf q 1271 = true := by
  have hs : count1270 q = (countLit q [-41, -42, -44]) + (countLit q [-45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -44]) (l₂ := [-45, -47, -48, -50])
  have hm := merge_right (literal (valuationOf q) (1267)) (literal (valuationOf q) (1271)) (countLit q [-41, -42, -44]) (countLit q [-45, -47, -48, -50]) (count1270 q) 2 (meaning1267 q) (meaning1271 q) hs
  change valuationOf q 1267 = false ∨ valuationOf q 1271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 1267 = false ∨ valuation q 1271 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 1259 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1272 = true := by
  have hs : count1270 q = (countLit q [-41, -42, -44]) + (countLit q [-45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -44]) (l₂ := [-45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1259)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1272)) (countLit q [-41, -42, -44]) (countLit q [-45, -47, -48, -50]) (count1270 q) 1 2 (meaning1259 q) (meaning1267 q) (meaning1272 q) hs
  change valuationOf q 1259 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 1259 = false ∨ valuation q 1267 = false ∨ valuation q 1272 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 1260 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1273 = true := by
  have hs : count1270 q = (countLit q [-41, -42, -44]) + (countLit q [-45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -44]) (l₂ := [-45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1260)) (literal (valuationOf q) (1267)) (literal (valuationOf q) (1273)) (countLit q [-41, -42, -44]) (countLit q [-45, -47, -48, -50]) (count1270 q) 2 2 (meaning1260 q) (meaning1267 q) (meaning1273 q) hs
  change valuationOf q 1260 = false ∨ valuationOf q 1267 = false ∨ valuationOf q 1273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 1260 = false ∨ valuation q 1267 = false ∨ valuation q 1273 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1271 = false ∨ valuationOf q 1280 = true := by
  have hs : count1277 q = (countLit q [-28, -29, -31, -34, -35, -38, -40]) + (countLit q [-41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -38, -40]) (l₂ := [-41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1271)) (literal (valuationOf q) (1280)) (countLit q [-28, -29, -31, -34, -35, -38, -40]) (countLit q [-41, -42, -44, -45, -47, -48, -50]) (count1277 q) 2 2 (meaning1251 q) (meaning1271 q) (meaning1280 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1271 = false ∨ valuationOf q 1280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1271 = false ∨ valuation q 1280 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1272 = false ∨ valuationOf q 1281 = true := by
  have hs : count1277 q = (countLit q [-28, -29, -31, -34, -35, -38, -40]) + (countLit q [-41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -38, -40]) (l₂ := [-41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1272)) (literal (valuationOf q) (1281)) (countLit q [-28, -29, -31, -34, -35, -38, -40]) (countLit q [-41, -42, -44, -45, -47, -48, -50]) (count1277 q) 2 3 (meaning1251 q) (meaning1272 q) (meaning1281 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1272 = false ∨ valuationOf q 1281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1272 = false ∨ valuation q 1281 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 1251 = false ∨ valuationOf q 1273 = false ∨ valuationOf q 1282 = true := by
  have hs : count1277 q = (countLit q [-28, -29, -31, -34, -35, -38, -40]) + (countLit q [-41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -31, -34, -35, -38, -40]) (l₂ := [-41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1251)) (literal (valuationOf q) (1273)) (literal (valuationOf q) (1282)) (countLit q [-28, -29, -31, -34, -35, -38, -40]) (countLit q [-41, -42, -44, -45, -47, -48, -50]) (count1277 q) 2 4 (meaning1251 q) (meaning1273 q) (meaning1282 q) hs
  change valuationOf q 1251 = false ∨ valuationOf q 1273 = false ∨ valuationOf q 1282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 1251 = false ∨ valuation q 1273 = false ∨ valuation q 1282 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1280 = false ∨ valuationOf q 1296 = true := by
  have hs : count1291 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) + (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (l₂ := [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1280)) (literal (valuationOf q) (1296)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (count1291 q) 2 4 (meaning1225 q) (meaning1280 q) (meaning1296 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1280 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1280 = false ∨ valuation q 1296 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1297 = true := by
  have hs : count1291 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) + (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (l₂ := [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1297)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (count1291 q) 2 5 (meaning1225 q) (meaning1281 q) (meaning1297 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1281 = false ∨ valuation q 1297 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 1225 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1298 = true := by
  have hs : count1291 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) + (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (l₂ := [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1225)) (literal (valuationOf q) (1282)) (literal (valuationOf q) (1298)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (count1291 q) 2 6 (meaning1225 q) (meaning1282 q) (meaning1298 q) hs
  change valuationOf q 1225 = false ∨ valuationOf q 1282 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 1225 = false ∨ valuation q 1282 = false ∨ valuation q 1298 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 1226 = false ∨ valuationOf q 1280 = false ∨ valuationOf q 1297 = true := by
  have hs : count1291 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) + (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (l₂ := [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1226)) (literal (valuationOf q) (1280)) (literal (valuationOf q) (1297)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (count1291 q) 3 4 (meaning1226 q) (meaning1280 q) (meaning1297 q) hs
  change valuationOf q 1226 = false ∨ valuationOf q 1280 = false ∨ valuationOf q 1297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 1226 = false ∨ valuation q 1280 = false ∨ valuation q 1297 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 1226 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1298 = true := by
  have hs : count1291 q = (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) + (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (l₂ := [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50])
  have hm := merge_two (literal (valuationOf q) (1226)) (literal (valuationOf q) (1281)) (literal (valuationOf q) (1298)) (countLit q [-3, -4, -5, -6, -10, -12, -13, -15, -17, -18, -20, -22, -27]) (countLit q [-28, -29, -31, -34, -35, -38, -40, -41, -42, -44, -45, -47, -48, -50]) (count1291 q) 3 5 (meaning1226 q) (meaning1281 q) (meaning1298 q) hs
  change valuationOf q 1226 = false ∨ valuationOf q 1281 = false ∨ valuationOf q 1298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 1226 = false ∨ valuation q 1281 = false ∨ valuation q 1298 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1306)) (countLit q [-57]) (countLit q [-58]) (count1306 q) 1 (meaningNeg58 q) (meaning1306 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1306 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1306 = true := by
  have hs : count1306 q = (countLit q [-57]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1306)) (countLit q [-57]) (countLit q [-58]) (count1306 q) 1 (meaningNeg57 q) (meaning1306 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1306 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1306 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 1306 = false ∨ valuationOf q 1308 = true := by
  have hs : count1308 q = (countLit q [-52]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-57, -58])
  have hm := merge_right (literal (valuationOf q) (1306)) (literal (valuationOf q) (1308)) (countLit q [-52]) (countLit q [-57, -58]) (count1308 q) 1 (meaning1306 q) (meaning1308 q) hs
  change valuationOf q 1306 = false ∨ valuationOf q 1308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 1306 = false ∨ valuation q 1308 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true := by
  have hs : count1308 q = (countLit q [-52]) + (countLit q [-57, -58]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-57, -58])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (1306)) (literal (valuationOf q) (1309)) (countLit q [-52]) (countLit q [-57, -58]) (count1308 q) 1 1 (meaningNeg52 q) (meaning1306 q) (meaning1309 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1306 = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1306 = false ∨ valuation q 1309 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-59]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1311)) (countLit q [-59]) (countLit q [-61]) (count1311 q) 1 (meaningNeg59 q) (meaning1311 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1311 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E242.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112242
