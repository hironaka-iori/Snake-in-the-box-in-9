import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [142, 143, 144]) + (countLit q [145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144]) (l₂ := [145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [142, 143, 144]) (countLit q [145, 146, 147, 148]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (289)) (countLit q [136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148]) (count289 q) 1 (meaning275 q) (meaning289 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 289 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (291)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning265 q) (meaning291 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 291 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (293)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning243 q) (meaning293 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 293 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 1 (meaning243 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (294)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 2 (meaning244 q) (meaning294 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 294 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_left (literal (valuationOf q) (150)) (literal (valuationOf q) (295)) (countLit q [150]) (countLit q [151]) (count295 q) 1 (meaning150 q) (meaning295 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 295 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [149]) (countLit q [150, 151]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_left (literal (valuationOf q) (153)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning153 q) (meaning299 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 299 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [152]) (countLit q [153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (301)) (countLit q [152]) (countLit q [153, 154]) (count301 q) 1 (meaning152 q) (meaning301 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 301 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (303)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154]) (count303 q) 1 (meaning297 q) (meaning303 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 303 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (315)) (countLit q [149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning303 q) (meaning315 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 315 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166, 167])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166, 167]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [161, 162, 163]) + (countLit q [165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [161, 162, 163]) (countLit q [165, 166, 167]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [161, 162, 163, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (337)) (countLit q [161, 162, 163, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173]) (count337 q) 1 (meaning325 q) (meaning337 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 337 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (339)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning315 q) (meaning339 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 339 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (341)) (countLit q [175]) (countLit q [176]) (count341 q) 1 (meaning175 q) (meaning341 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 341 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175, 176])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [174]) (countLit q [175, 176]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (349)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179]) (count349 q) 1 (meaning343 q) (meaning349 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 349 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184, 185]) (count357 q) 1 (meaning183 q) (meaning357 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 357 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [180, 181, 182]) + (countLit q [183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182]) (l₂ := [183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [180, 181, 182]) (countLit q [183, 184, 185]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (361)) (countLit q [174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185]) (count361 q) 1 (meaning349 q) (meaning361 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 361 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning188 q) (meaning363 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 363 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [190]) + (countLit q [191]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191])
  have hm := merge_left (literal (valuationOf q) (190)) (literal (valuationOf q) (367)) (countLit q [190]) (countLit q [191]) (count367 q) 1 (meaning190 q) (meaning367 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 367 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190, 191])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [189]) (countLit q [190, 191]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E170.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112170
