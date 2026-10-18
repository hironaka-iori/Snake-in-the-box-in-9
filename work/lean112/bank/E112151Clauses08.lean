import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (305)) (countLit q [158]) (countLit q [159]) (count305 q) 1 (meaning158 q) (meaning305 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 305 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (309)) (countLit q [158, 159]) (countLit q [160, 161]) (count309 q) 1 (meaning305 q) (meaning309 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 309 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (317)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning263 q) (meaning317 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 317 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161])
  have hm := merge_two (literal (valuationOf q) (263)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 1 (meaning263 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (264)) (literal (valuationOf q) (318)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (count317 q) 2 (meaning264 q) (meaning318 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 318 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_right (literal (valuationOf q) (167)) (literal (valuationOf q) (323)) (countLit q [166]) (countLit q [167]) (count323 q) 1 (meaning167 q) (meaning323 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 323 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [165]) (countLit q [166, 167]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (341)) (countLit q [162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning327 q) (meaning341 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 341 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (343)) (countLit q [176]) (countLit q [177]) (count343 q) 1 (meaning176 q) (meaning343 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 343 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [175]) (countLit q [176, 177]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (349)) (countLit q [178]) (countLit q [179, 180]) (count349 q) 1 (meaning178 q) (meaning349 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 349 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (351)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180]) (count351 q) 1 (meaning345 q) (meaning351 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 351 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (365)) (countLit q [175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187]) (count365 q) 1 (meaning351 q) (meaning365 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 365 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (367)) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]) (count367 q) 1 (meaning341 q) (meaning367 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 367 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (369)) (countLit q [189]) (countLit q [190]) (count369 q) 1 (meaning189 q) (meaning369 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 369 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [188]) (countLit q [189, 190]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuationOf q) (193)) (literal (valuationOf q) (373)) (countLit q [192]) (countLit q [193]) (count373 q) 1 (meaning193 q) (meaning373 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 373 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192, 193]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192, 193])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192, 193]) (count375 q) 1 (meaning191 q) (meaning375 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 375 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [188, 189, 190]) + (countLit q [191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190]) (l₂ := [191, 192, 193])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [188, 189, 190]) (countLit q [191, 192, 193]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [188, 189, 190]) + (countLit q [191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190]) (l₂ := [191, 192, 193])
  have hm := merge_left (literal (valuationOf q) (371)) (literal (valuationOf q) (377)) (countLit q [188, 189, 190]) (countLit q [191, 192, 193]) (count377 q) 1 (meaning371 q) (meaning377 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 377 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [188, 189, 190]) + (countLit q [191, 192, 193]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190]) (l₂ := [191, 192, 193])
  have hm := merge_two (literal (valuationOf q) (371)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [188, 189, 190]) (countLit q [191, 192, 193]) (count377 q) 1 1 (meaning371 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (383)) (countLit q [197]) (countLit q [198]) (count383 q) 1 (meaning198 q) (meaning383 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 383 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [197, 198]) + (countLit q [199, 200]) := List.countP_append (p := literal q) (l₁ := [197, 198]) (l₂ := [199, 200])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (387)) (countLit q [197, 198]) (countLit q [199, 200]) (count387 q) 1 (meaning383 q) (meaning387 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 387 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [194, 195, 196]) + (countLit q [197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [194, 195, 196]) (l₂ := [197, 198, 199, 200])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [194, 195, 196]) (countLit q [197, 198, 199, 200]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 391 = true := by
  have hs : count391 q = (countLit q [188, 189, 190, 191, 192, 193]) + (countLit q [194, 195, 196, 197, 198, 199, 200]) := List.countP_append (p := literal q) (l₁ := [188, 189, 190, 191, 192, 193]) (l₂ := [194, 195, 196, 197, 198, 199, 200])
  have hm := merge_left (literal (valuationOf q) (377)) (literal (valuationOf q) (391)) (countLit q [188, 189, 190, 191, 192, 193]) (countLit q [194, 195, 196, 197, 198, 199, 200]) (count391 q) 1 (meaning377 q) (meaning391 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 391 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E151.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112151
