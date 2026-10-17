import E112182Semantics
import B112E182Inputs
namespace Snake9.Regrowth.E112182
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1295)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 1 2 (meaning1271 q) (meaning1288 q) (meaning1295 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1288 = false ∨ valuation q 1295 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 1271 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1296 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1271)) (literal (valuationOf q) (1289)) (literal (valuationOf q) (1296)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 1 3 (meaning1271 q) (meaning1289 q) (meaning1296 q) hs
  change valuationOf q 1271 = false ∨ valuationOf q 1289 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 1271 = false ∨ valuation q 1289 = false ∨ valuation q 1296 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1294 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1272)) (literal (valuationOf q) (1294)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 2 (meaning1272 q) (meaning1294 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1294 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1287 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1287)) (literal (valuationOf q) (1295)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 2 1 (meaning1272 q) (meaning1287 q) (meaning1295 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1287 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1287 = false ∨ valuation q 1295 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 1272 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1296 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1272)) (literal (valuationOf q) (1288)) (literal (valuationOf q) (1296)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 2 2 (meaning1272 q) (meaning1288 q) (meaning1296 q) hs
  change valuationOf q 1272 = false ∨ valuationOf q 1288 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 1272 = false ∨ valuation q 1288 = false ∨ valuation q 1296 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1295 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_left (literal (valuationOf q) (1273)) (literal (valuationOf q) (1295)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 3 (meaning1273 q) (meaning1295 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1295 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 1273 = false ∨ valuationOf q 1287 = false ∨ valuationOf q 1296 = true := by
  have hs : count1293 q = (countLit q [-28, -29, -36, -37, -38, -40]) + (countLit q [-42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -36, -37, -38, -40]) (l₂ := [-42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1273)) (literal (valuationOf q) (1287)) (literal (valuationOf q) (1296)) (countLit q [-28, -29, -36, -37, -38, -40]) (countLit q [-42, -45, -48, -50, -52, -53]) (count1293 q) 3 1 (meaning1273 q) (meaning1287 q) (meaning1296 q) hs
  change valuationOf q 1273 = false ∨ valuationOf q 1287 = false ∨ valuationOf q 1296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 1273 = false ∨ valuation q 1287 = false ∨ valuation q 1296 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 1294 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1294)) (literal (valuationOf q) (1302)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 2 (meaning1294 q) (meaning1302 q) hs
  change valuationOf q 1294 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 1294 = false ∨ valuation q 1302 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 1295 = false ∨ valuationOf q 1303 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1295)) (literal (valuationOf q) (1303)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 3 (meaning1295 q) (meaning1303 q) hs
  change valuationOf q 1295 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 1295 = false ∨ valuation q 1303 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 1296 = false ∨ valuationOf q 1304 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_right (literal (valuationOf q) (1296)) (literal (valuationOf q) (1304)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 4 (meaning1296 q) (meaning1304 q) hs
  change valuationOf q 1296 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 1296 = false ∨ valuation q 1304 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1302 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1293)) (literal (valuationOf q) (1302)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 1 1 (meaning1253 q) (meaning1293 q) (meaning1302 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1293 = false ∨ valuation q 1302 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1294 = false ∨ valuationOf q 1303 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1294)) (literal (valuationOf q) (1303)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 1 2 (meaning1253 q) (meaning1294 q) (meaning1303 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1294 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1294 = false ∨ valuation q 1303 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1304 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1304)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 1 3 (meaning1253 q) (meaning1295 q) (meaning1304 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1295 = false ∨ valuation q 1304 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 1253 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1305 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1253)) (literal (valuationOf q) (1296)) (literal (valuationOf q) (1305)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 1 4 (meaning1253 q) (meaning1296 q) (meaning1305 q) hs
  change valuationOf q 1253 = false ∨ valuationOf q 1296 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 1253 = false ∨ valuation q 1296 = false ∨ valuation q 1305 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1303 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1293)) (literal (valuationOf q) (1303)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 2 1 (meaning1254 q) (meaning1293 q) (meaning1303 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1293 = false ∨ valuationOf q 1303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1293 = false ∨ valuation q 1303 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1294 = false ∨ valuationOf q 1304 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1294)) (literal (valuationOf q) (1304)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 2 2 (meaning1254 q) (meaning1294 q) (meaning1304 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1294 = false ∨ valuationOf q 1304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1294 = false ∨ valuation q 1304 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 1254 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1305 = true := by
  have hs : count1301 q = (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) + (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) := List.countP_append (p := literal q) (l₁ := [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (l₂ := [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53])
  have hm := merge_two (literal (valuationOf q) (1254)) (literal (valuationOf q) (1295)) (literal (valuationOf q) (1305)) (countLit q [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]) (countLit q [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]) (count1301 q) 2 3 (meaning1254 q) (meaning1295 q) (meaning1305 q) hs
  change valuationOf q 1254 = false ∨ valuationOf q 1295 = false ∨ valuationOf q 1305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 1254 = false ∨ valuation q 1295 = false ∨ valuation q 1305 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1309)) (countLit q [-58]) (countLit q [-60]) (count1309 q) 1 (meaningNeg60 q) (meaning1309 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1309 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1309 = true := by
  have hs : count1309 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1309)) (countLit q [-58]) (countLit q [-60]) (count1309 q) 1 (meaningNeg58 q) (meaning1309 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1309 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1309 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 1309 = false ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-54]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-58, -60])
  have hm := merge_right (literal (valuationOf q) (1309)) (literal (valuationOf q) (1311)) (countLit q [-54]) (countLit q [-58, -60]) (count1311 q) 1 (meaning1309 q) (meaning1311 q) hs
  change valuationOf q 1309 = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 1309 = false ∨ valuation q 1311 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1311 = true := by
  have hs : count1311 q = (countLit q [-54]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-58, -60])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1311)) (countLit q [-54]) (countLit q [-58, -60]) (count1311 q) 1 (meaningNeg54 q) (meaning1311 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1311 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1311 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1309 = false ∨ valuationOf q 1312 = true := by
  have hs : count1311 q = (countLit q [-54]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-58, -60])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (1309)) (literal (valuationOf q) (1312)) (countLit q [-54]) (countLit q [-58, -60]) (count1311 q) 1 1 (meaningNeg54 q) (meaning1309 q) (meaning1312 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1309 = false ∨ valuationOf q 1312 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1309 = false ∨ valuation q 1312 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1314)) (countLit q [-64]) (countLit q [-66]) (count1314 q) 1 (meaningNeg66 q) (meaning1314 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1314 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1314 = true := by
  have hs : count1314 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1314)) (countLit q [-64]) (countLit q [-66]) (count1314 q) 1 (meaningNeg64 q) (meaning1314 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1314 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1314 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1316 = true := by
  have hs : count1316 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1316)) (countLit q [-63]) (countLit q [-64, -66]) (count1316 q) 1 (meaningNeg63 q) (meaning1316 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1316 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1316 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true := by
  have hs : count1316 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1314)) (literal (valuationOf q) (1317)) (countLit q [-63]) (countLit q [-64, -66]) (count1316 q) 1 1 (meaningNeg63 q) (meaning1314 q) (meaning1317 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1314 = false ∨ valuationOf q 1317 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1314 = false ∨ valuation q 1317 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 1316 = false ∨ valuationOf q 1319 = true := by
  have hs : count1319 q = (countLit q [-54, -58, -60]) + (countLit q [-63, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60]) (l₂ := [-63, -64, -66])
  have hm := merge_right (literal (valuationOf q) (1316)) (literal (valuationOf q) (1319)) (countLit q [-54, -58, -60]) (countLit q [-63, -64, -66]) (count1319 q) 1 (meaning1316 q) (meaning1319 q) hs
  change valuationOf q 1316 = false ∨ valuationOf q 1319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 1316 = false ∨ valuation q 1319 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 1317 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-54, -58, -60]) + (countLit q [-63, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60]) (l₂ := [-63, -64, -66])
  have hm := merge_right (literal (valuationOf q) (1317)) (literal (valuationOf q) (1320)) (countLit q [-54, -58, -60]) (countLit q [-63, -64, -66]) (count1319 q) 2 (meaning1317 q) (meaning1320 q) hs
  change valuationOf q 1317 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 1317 = false ∨ valuation q 1320 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1320 = true := by
  have hs : count1319 q = (countLit q [-54, -58, -60]) + (countLit q [-63, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60]) (l₂ := [-63, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1320)) (countLit q [-54, -58, -60]) (countLit q [-63, -64, -66]) (count1319 q) 1 1 (meaning1311 q) (meaning1316 q) (meaning1320 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1316 = false ∨ valuation q 1320 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 1311 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-54, -58, -60]) + (countLit q [-63, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60]) (l₂ := [-63, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1311)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1321)) (countLit q [-54, -58, -60]) (countLit q [-63, -64, -66]) (count1319 q) 1 2 (meaning1311 q) (meaning1317 q) (meaning1321 q) hs
  change valuationOf q 1311 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 1311 = false ∨ valuation q 1317 = false ∨ valuation q 1321 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true := by
  have hs : count1319 q = (countLit q [-54, -58, -60]) + (countLit q [-63, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60]) (l₂ := [-63, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1316)) (literal (valuationOf q) (1321)) (countLit q [-54, -58, -60]) (countLit q [-63, -64, -66]) (count1319 q) 2 1 (meaning1312 q) (meaning1316 q) (meaning1321 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1316 = false ∨ valuationOf q 1321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1316 = false ∨ valuation q 1321 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 1312 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true := by
  have hs : count1319 q = (countLit q [-54, -58, -60]) + (countLit q [-63, -64, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -58, -60]) (l₂ := [-63, -64, -66])
  have hm := merge_two (literal (valuationOf q) (1312)) (literal (valuationOf q) (1317)) (literal (valuationOf q) (1322)) (countLit q [-54, -58, -60]) (countLit q [-63, -64, -66]) (count1319 q) 2 2 (meaning1312 q) (meaning1317 q) (meaning1322 q) hs
  change valuationOf q 1312 = false ∨ valuationOf q 1317 = false ∨ valuationOf q 1322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 1312 = false ∨ valuation q 1317 = false ∨ valuation q 1322 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E182.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112182
