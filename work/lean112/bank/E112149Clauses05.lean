import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (290)) (countLit q [136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148]) (count289 q) 2 (meaning276 q) (meaning290 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 290 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (290)) (literal (valuationOf q) (292)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 2 (meaning290 q) (meaning292 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 292 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (291)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 (meaning265 q) (meaning291 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 291 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (289)) (literal (valuationOf q) (292)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 1 1 (meaning265 q) (meaning289 q) (meaning292 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 289 = false ∨ valuation q 292 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (292)) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count291 q) 2 (meaning266 q) (meaning292 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 292 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (293)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 (meaning243 q) (meaning293 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 293 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (243)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 1 1 (meaning243 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (244)) (literal (valuationOf q) (294)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (count293 q) 2 (meaning244 q) (meaning294 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 294 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150, 151])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (297)) (countLit q [149]) (countLit q [150, 151]) (count297 q) 1 (meaning149 q) (meaning297 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 297 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [149, 150, 151]) + (countLit q [152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151]) (l₂ := [152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (303)) (countLit q [149, 150, 151]) (countLit q [152, 153, 154]) (count303 q) 1 (meaning297 q) (meaning303 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 303 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (309)) (countLit q [159]) (countLit q [160]) (count309 q) 1 (meaning160 q) (meaning309 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 309 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [158]) (countLit q [159, 160]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (315)) (countLit q [149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning303 q) (meaning315 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 315 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_right (literal (valuationOf q) (163)) (literal (valuationOf q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning163 q) (meaning317 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 317 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [161]) (countLit q [162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (319)) (countLit q [161]) (countLit q [162, 163]) (count319 q) 1 (meaning161 q) (meaning319 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 319 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (321)) (countLit q [165]) (countLit q [166]) (count321 q) 1 (meaning165 q) (meaning321 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 321 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [164]) (countLit q [165, 166]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (325)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166]) (count325 q) 1 (meaning319 q) (meaning325 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 325 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (329)) (countLit q [167]) (countLit q [169, 170]) (count329 q) 1 (meaning167 q) (meaning329 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 329 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_right (literal (valuationOf q) (173)) (literal (valuationOf q) (331)) (countLit q [172]) (countLit q [173]) (count331 q) 1 (meaning173 q) (meaning331 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 331 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [171]) (countLit q [172, 173]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [167, 169, 170]) + (countLit q [171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 169, 170]) (l₂ := [171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [167, 169, 170]) (countLit q [171, 172, 173]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [167, 169, 170]) + (countLit q [171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [167, 169, 170]) (l₂ := [171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (335)) (countLit q [167, 169, 170]) (countLit q [171, 172, 173]) (count335 q) 1 (meaning329 q) (meaning335 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 335 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [161, 162, 163, 164, 165, 166]) + (countLit q [167, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166]) (l₂ := [167, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [161, 162, 163, 164, 165, 166]) (countLit q [167, 169, 170, 171, 172, 173]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [161, 162, 163, 164, 165, 166]) + (countLit q [167, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166]) (l₂ := [167, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (337)) (countLit q [161, 162, 163, 164, 165, 166]) (countLit q [167, 169, 170, 171, 172, 173]) (count337 q) 1 (meaning325 q) (meaning337 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 337 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E149.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112149
