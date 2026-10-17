import E112183Semantics
import B112E183Inputs
namespace Snake9.Regrowth.E112183
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [151, 152, 153, 154, 155, 156, 157]) + (countLit q [159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154, 155, 156, 157]) (l₂ := [159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (321)) (countLit q [151, 152, 153, 154, 155, 156, 157]) (countLit q [159, 160, 161, 162, 163, 164, 165]) (count321 q) 1 (meaning307 q) (meaning321 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 321 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [151, 152, 153, 154, 155, 156, 157]) + (countLit q [159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154, 155, 156, 157]) (l₂ := [159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (322)) (countLit q [151, 152, 153, 154, 155, 156, 157]) (countLit q [159, 160, 161, 162, 163, 164, 165]) (count321 q) 2 (meaning308 q) (meaning322 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 322 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (322)) (literal (valuationOf q) (324)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 2 (meaning322 q) (meaning324 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 324 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (323)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 1 (meaning295 q) (meaning323 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 323 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (324)) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 2 (meaning296 q) (meaning324 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 324 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (324)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 2 (meaning324 q) (meaning326 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 326 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (325)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 1 (meaning271 q) (meaning325 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 325 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 323 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (323)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 1 1 (meaning271 q) (meaning323 q) (meaning326 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 323 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 323 = false ∨ valuation q 326 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 2 (meaning272 q) (meaning326 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 326 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (327)) (countLit q [167]) (countLit q [168]) (count327 q) 1 (meaning168 q) (meaning327 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 327 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (327)) (countLit q [167]) (countLit q [168]) (count327 q) 1 (meaning167 q) (meaning327 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 327 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [166]) (countLit q [167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (329)) (countLit q [166]) (countLit q [167, 168]) (count329 q) 1 (meaning166 q) (meaning329 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 329 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [169]) (countLit q [170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (335)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171]) (count335 q) 1 (meaning329 q) (meaning335 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 335 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171]) (count335 q) 1 1 (meaning329 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [172]) (countLit q [173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (341)) (countLit q [175]) (countLit q [176]) (count341 q) 1 (meaning175 q) (meaning341 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 341 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning178 q) (meaning343 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 343 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning341 q) (meaning345 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 345 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (347)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning339 q) (meaning347 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 347 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 1 (meaning339 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (349)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning335 q) (meaning349 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 349 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E183.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112183
