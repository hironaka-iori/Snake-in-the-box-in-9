import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (302)) (literal (valuationOf q) (304)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning302 q) (meaning304 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 304 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (303)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning289 q) (meaning303 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 303 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 1 (meaning289 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (305)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning279 q) (meaning305 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 305 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (303)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 1 (meaning279 q) (meaning303 q) (meaning306 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 303 = false ∨ valuation q 306 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (280)) (literal (valuationOf q) (306)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning280 q) (meaning306 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 306 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (306)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 2 (meaning306 q) (meaning308 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 308 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (307)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 1 (meaning255 q) (meaning307 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 307 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 1 1 (meaning255 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (256)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count307 q) 2 (meaning256 q) (meaning308 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 308 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (309)) (countLit q [157]) (countLit q [158]) (count309 q) 1 (meaning157 q) (meaning309 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 309 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [156]) (countLit q [157, 158]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (313)) (countLit q [160]) (countLit q [161]) (count313 q) 1 (meaning160 q) (meaning313 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 313 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160, 161])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [159]) (countLit q [160, 161]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161]) (count317 q) 1 (meaning311 q) (meaning317 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 317 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161]) (count317 q) 1 1 (meaning311 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning163 q) (meaning319 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 319 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning162 q) (meaning321 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 321 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 319 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_two (literal (valuationOf q) (162)) (literal (valuationOf q) (319)) (literal (valuationOf q) (322)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 1 (meaning162 q) (meaning319 q) (meaning322 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 319 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 319 = false ∨ valuation q 322 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (325)) (countLit q [167]) (countLit q [168]) (count325 q) 1 (meaning168 q) (meaning325 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 325 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (327)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 (meaning323 q) (meaning327 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 327 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (literal (valuationOf q) (328)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 1 (meaning323 q) (meaning325 q) (meaning328 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = false ∨ valuation q 328 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (328)) (literal (valuationOf q) (330)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 2 (meaning328 q) (meaning330 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 330 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning321 q) (meaning329 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 329 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E174.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112174
