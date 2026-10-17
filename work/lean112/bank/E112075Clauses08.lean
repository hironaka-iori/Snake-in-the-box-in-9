import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (309)) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count309 q) 1 (meaning283 q) (meaning309 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 309 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (311)) (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 1 (meaning259 q) (meaning311 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 311 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157])
  have hm := merge_two (literal (valuationOf q) (259)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (count311 q) 1 1 (meaning259 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (327)) (countLit q [167]) (countLit q [168]) (count327 q) 1 (meaning168 q) (meaning327 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 327 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (331)) (countLit q [167, 168]) (countLit q [169, 170]) (count331 q) 1 (meaning327 q) (meaning331 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 331 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172, 173])
  have hm := merge_left (literal (valuationOf q) (171)) (literal (valuationOf q) (339)) (countLit q [171]) (countLit q [172, 173]) (count339 q) 1 (meaning171 q) (meaning339 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 339 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (343)) (countLit q [175]) (countLit q [176, 177]) (count343 q) 1 (meaning175 q) (meaning343 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 343 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [171, 172, 173]) + (countLit q [175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [171, 172, 173]) (countLit q [175, 176, 177]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [171, 172, 173]) + (countLit q [175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (345)) (countLit q [171, 172, 173]) (countLit q [175, 176, 177]) (count345 q) 1 (meaning339 q) (meaning345 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 345 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_right (literal (valuationOf q) (180)) (literal (valuationOf q) (347)) (countLit q [179]) (countLit q [180]) (count347 q) 1 (meaning180 q) (meaning347 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 347 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179, 180])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [178]) (countLit q [179, 180]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_right (literal (valuationOf q) (182)) (literal (valuationOf q) (351)) (countLit q [181]) (countLit q [182]) (count351 q) 1 (meaning182 q) (meaning351 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 351 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (355)) (countLit q [181, 182]) (countLit q [183, 184]) (count355 q) 1 (meaning351 q) (meaning355 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 355 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183, 184]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (357)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183, 184]) (count357 q) 1 (meaning349 q) (meaning357 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 357 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [171, 172, 173, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [171, 172, 173, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [171, 172, 173, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (359)) (countLit q [171, 172, 173, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184]) (count359 q) 1 (meaning345 q) (meaning359 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 359 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [171, 172, 173, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184])
  have hm := merge_two (literal (valuationOf q) (345)) (literal (valuationOf q) (357)) (literal (valuationOf q) (360)) (countLit q [171, 172, 173, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184]) (count359 q) 1 1 (meaning345 q) (meaning357 q) (meaning360 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 357 = false ∨ valuation q 360 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (360)) (literal (valuationOf q) (362)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (count361 q) 2 (meaning360 q) (meaning362 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 362 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (361)) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184]) (count361 q) 1 (meaning335 q) (meaning361 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 361 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [186]) + (countLit q [187]) := List.countP_append (p := literal q) (l₁ := [186]) (l₂ := [187])
  have hm := merge_left (literal (valuationOf q) (186)) (literal (valuationOf q) (363)) (countLit q [186]) (countLit q [187]) (count363 q) 1 (meaning186 q) (meaning363 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 363 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186, 187])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [185]) (countLit q [186, 187]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [185, 186, 187]) + (countLit q [188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187]) (l₂ := [188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (371)) (countLit q [185, 186, 187]) (countLit q [188, 189, 190]) (count371 q) 1 (meaning365 q) (meaning371 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 371 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_left (literal (valuationOf q) (196)) (literal (valuationOf q) (379)) (countLit q [196]) (countLit q [197]) (count379 q) 1 (meaning196 q) (meaning379 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 379 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [194, 195]) (countLit q [196, 197]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196, 197]) (count383 q) 1 (meaning381 q) (meaning383 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E075.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112075
