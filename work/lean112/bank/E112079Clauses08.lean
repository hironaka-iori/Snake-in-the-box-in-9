import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (305)) (countLit q [154, 155]) (countLit q [156, 157]) (count305 q) 1 (meaning301 q) (meaning305 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 305 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (307)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count307 q) 1 (meaning299 q) (meaning307 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 307 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (313)) (countLit q [161]) (countLit q [162]) (count313 q) 1 (meaning161 q) (meaning313 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 313 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (315)) (countLit q [163]) (countLit q [164]) (count315 q) 1 (meaning163 q) (meaning315 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 315 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [161, 162]) (countLit q [163, 164]) (count317 q) 1 1 (meaning313 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (318)) (literal (valuationOf q) (320)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163, 164]) (count319 q) 2 (meaning318 q) (meaning320 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 320 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (320)) (literal (valuationOf q) (322)) (countLit q [151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164]) (count321 q) 2 (meaning320 q) (meaning322 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 322 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (321)) (countLit q [151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164]) (count321 q) 1 (meaning307 q) (meaning321 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 321 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (322)) (literal (valuationOf q) (324)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count323 q) 2 (meaning322 q) (meaning324 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 324 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (323)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count323 q) 1 (meaning295 q) (meaning323 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 323 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (321)) (literal (valuationOf q) (324)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count323 q) 1 1 (meaning295 q) (meaning321 q) (meaning324 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 321 = false ∨ valuation q 324 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (324)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count323 q) 2 (meaning296 q) (meaning324 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 324 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (324)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count325 q) 2 (meaning324 q) (meaning326 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 326 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (325)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count325 q) 1 (meaning271 q) (meaning325 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 325 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 323 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (323)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count325 q) 1 1 (meaning271 q) (meaning323 q) (meaning326 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 323 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 323 = false ∨ valuation q 326 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (count325 q) 2 (meaning272 q) (meaning326 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 326 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_right (literal (valuationOf q) (173)) (literal (valuationOf q) (337)) (countLit q [172]) (countLit q [173]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172, 173])
  have hm := merge_two (literal (valuationOf q) (171)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [171]) (countLit q [172, 173]) (count339 q) 1 1 (meaning171 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (340)) (literal (valuationOf q) (348)) (countLit q [171, 172, 173]) (countLit q [174, 175, 176, 177]) (count347 q) 2 (meaning340 q) (meaning348 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 348 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 184 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_two (literal (valuationOf q) (183)) (literal (valuationOf q) (184)) (literal (valuationOf q) (358)) (countLit q [183]) (countLit q [184]) (count357 q) 1 1 (meaning183 q) (meaning184 q) (meaning358 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 184 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 184 = false ∨ valuation q 358 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 358 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (358)) (literal (valuationOf q) (360)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 2 (meaning358 q) (meaning360 q) hs
  change valuationOf q 358 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 360 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (360)) (literal (valuationOf q) (362)) (countLit q [178, 179, 180]) (countLit q [181, 182, 183, 184]) (count361 q) 2 (meaning360 q) (meaning362 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 362 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189])
  have hm := merge_right (literal (valuationOf q) (189)) (literal (valuationOf q) (367)) (countLit q [188]) (countLit q [189]) (count367 q) 1 (meaning189 q) (meaning367 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 367 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [188, 189]) + (countLit q [190, 191]) := List.countP_append (p := literal q) (l₁ := [188, 189]) (l₂ := [190, 191])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (371)) (countLit q [188, 189]) (countLit q [190, 191]) (count371 q) 1 (meaning367 q) (meaning371 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 371 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [185, 186, 187]) + (countLit q [188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187]) (l₂ := [188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [185, 186, 187]) (countLit q [188, 189, 190, 191]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 362 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191])
  have hm := merge_left (literal (valuationOf q) (362)) (literal (valuationOf q) (376)) (countLit q [178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191]) (count375 q) 2 (meaning362 q) (meaning376 q) hs
  change valuationOf q 362 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 362 = false ∨ valuation q 376 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) + (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (l₂ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E079.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112079
