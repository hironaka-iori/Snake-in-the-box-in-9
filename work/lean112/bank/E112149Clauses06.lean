import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (339)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning315 q) (meaning339 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 339 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173])
  have hm := merge_two (literal (valuationOf q) (315)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (count339 q) 1 1 (meaning315 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_right (literal (valuationOf q) (182)) (literal (valuationOf q) (351)) (countLit q [181]) (countLit q [182]) (count351 q) 1 (meaning182 q) (meaning351 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 351 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181, 182])
  have hm := merge_two (literal (valuationOf q) (180)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [180]) (countLit q [181, 182]) (count353 q) 1 1 (meaning180 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [180, 181, 182]) + (countLit q [183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182]) (l₂ := [183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (354)) (literal (valuationOf q) (360)) (countLit q [180, 181, 182]) (countLit q [183, 184, 185]) (count359 q) 2 (meaning354 q) (meaning360 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 360 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [174, 175, 176, 177, 178, 179]) + (countLit q [180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179]) (l₂ := [180, 181, 182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (360)) (literal (valuationOf q) (362)) (countLit q [174, 175, 176, 177, 178, 179]) (countLit q [180, 181, 182, 183, 184, 185]) (count361 q) 2 (meaning360 q) (meaning362 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 362 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning188 q) (meaning363 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 363 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [186, 187, 188]) + (countLit q [189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188]) (l₂ := [189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (371)) (countLit q [186, 187, 188]) (countLit q [189, 190, 191]) (count371 q) 1 (meaning365 q) (meaning371 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 371 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (385)) (countLit q [186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198]) (count385 q) 1 (meaning371 q) (meaning385 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 385 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) + (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (l₂ := [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (388)) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]) (countLit q [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count387 q) 2 (meaning362 q) (meaning388 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 388 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (388)) (literal (valuationOf q) (390)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count389 q) 2 (meaning388 q) (meaning390 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 390 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (389)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count389 q) 1 (meaning339 q) (meaning389 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 389 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (387)) (literal (valuationOf q) (390)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count389 q) 1 1 (meaning339 q) (meaning387 q) (meaning390 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 387 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 387 = false ∨ valuation q 390 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) + (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (l₂ := [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (340)) (literal (valuationOf q) (390)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173]) (countLit q [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count389 q) 2 (meaning340 q) (meaning390 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 390 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 390 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (390)) (literal (valuationOf q) (392)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count391 q) 2 (meaning390 q) (meaning392 q) hs
  change valuationOf q 390 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 390 = false ∨ valuation q 392 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (389)) (literal (valuationOf q) (392)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count391 q) 1 1 (meaning293 q) (meaning389 q) (meaning392 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 389 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 389 = false ∨ valuation q 392 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 392 = true := by
  have hs : count391 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (392)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]) (count391 q) 2 (meaning294 q) (meaning392 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 392 = true := counterClause212 (baseVal q)

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 392 = false := by
  rw [value392]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count391 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause214 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1149 = true := by
  have hs : count1149 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1149)) (countLit q [-3]) (countLit q [-6]) (count1149 q) 1 (meaningNeg6 q) (meaning1149 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1149 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1149 = true := by
  have hs : count1149 q = (countLit q [-3]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1149)) (countLit q [-3]) (countLit q [-6]) (count1149 q) 1 (meaningNeg3 q) (meaning1149 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1149 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 1149 = false ∨ valuationOf q 1151 = true := by
  have hs : count1151 q = (countLit q [-2]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -6])
  have hm := merge_right (literal (valuationOf q) (1149)) (literal (valuationOf q) (1151)) (countLit q [-2]) (countLit q [-3, -6]) (count1151 q) 1 (meaning1149 q) (meaning1151 q) hs
  change valuationOf q 1149 = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 1149 = false ∨ valuation q 1151 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1151 = true := by
  have hs : count1151 q = (countLit q [-2]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1151)) (countLit q [-2]) (countLit q [-3, -6]) (count1151 q) 1 (meaningNeg2 q) (meaning1151 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1151 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1149 = false ∨ valuationOf q 1152 = true := by
  have hs : count1151 q = (countLit q [-2]) + (countLit q [-3, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -6])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1149)) (literal (valuationOf q) (1152)) (countLit q [-2]) (countLit q [-3, -6]) (count1151 q) 1 1 (meaningNeg2 q) (meaning1149 q) (meaning1152 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1149 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1149 = false ∨ valuation q 1152 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1154 = true := by
  have hs : count1154 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1154)) (countLit q [-9]) (countLit q [-10]) (count1154 q) 1 (meaningNeg10 q) (meaning1154 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1154 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 1154 = false ∨ valuationOf q 1156 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (1154)) (literal (valuationOf q) (1156)) (countLit q [-8]) (countLit q [-9, -10]) (count1156 q) 1 (meaning1154 q) (meaning1156 q) hs
  change valuationOf q 1154 = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 1154 = false ∨ valuation q 1156 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1156 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1156)) (countLit q [-8]) (countLit q [-9, -10]) (count1156 q) 1 (meaningNeg8 q) (meaning1156 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1156 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1156 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1154 = false ∨ valuationOf q 1157 = true := by
  have hs : count1156 q = (countLit q [-8]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9, -10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1154)) (literal (valuationOf q) (1157)) (countLit q [-8]) (countLit q [-9, -10]) (count1156 q) 1 1 (meaningNeg8 q) (meaning1154 q) (meaning1157 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1154 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1154 = false ∨ valuation q 1157 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 1157 = false ∨ valuationOf q 1160 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -6]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6]) (l₂ := [-8, -9, -10])
  have hm := merge_right (literal (valuationOf q) (1157)) (literal (valuationOf q) (1160)) (countLit q [-2, -3, -6]) (countLit q [-8, -9, -10]) (count1159 q) 2 (meaning1157 q) (meaning1160 q) hs
  change valuationOf q 1157 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 1157 = false ∨ valuation q 1160 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 1151 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1160 = true := by
  have hs : count1159 q = (countLit q [-2, -3, -6]) + (countLit q [-8, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -6]) (l₂ := [-8, -9, -10])
  have hm := merge_two (literal (valuationOf q) (1151)) (literal (valuationOf q) (1156)) (literal (valuationOf q) (1160)) (countLit q [-2, -3, -6]) (countLit q [-8, -9, -10]) (count1159 q) 1 1 (meaning1151 q) (meaning1156 q) (meaning1160 q) hs
  change valuationOf q 1151 = false ∨ valuationOf q 1156 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 1151 = false ∨ valuation q 1156 = false ∨ valuation q 1160 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E149.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112149
