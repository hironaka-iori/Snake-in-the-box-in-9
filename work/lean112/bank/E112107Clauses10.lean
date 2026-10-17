import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (320)) (literal (valuationOf q) (322)) (countLit q [152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165]) (count321 q) 2 (meaning320 q) (meaning322 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 322 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (322)) (literal (valuationOf q) (324)) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 2 (meaning322 q) (meaning324 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 324 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (323)) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 1 (meaning295 q) (meaning323 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 323 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (321)) (literal (valuationOf q) (324)) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 1 1 (meaning295 q) (meaning321 q) (meaning324 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 321 = false ∨ valuation q 324 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (324)) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count323 q) 2 (meaning296 q) (meaning324 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 324 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (324)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 2 (meaning324 q) (meaning326 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 326 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (325)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 1 (meaning271 q) (meaning325 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 325 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 323 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (323)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 1 1 (meaning271 q) (meaning323 q) (meaning326 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 323 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 323 = false ∨ valuation q 326 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) + (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (l₂ := [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (326)) (countLit q [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]) (countLit q [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]) (count325 q) 2 (meaning272 q) (meaning326 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 326 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (329)) (countLit q [166]) (countLit q [167, 168]) (count329 q) 1 (meaning166 q) (meaning329 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 329 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (333)) (countLit q [169]) (countLit q [170, 171]) (count333 q) 1 (meaning169 q) (meaning333 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 333 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (335)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171]) (count335 q) 1 (meaning329 q) (meaning335 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 335 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171]) (count335 q) 1 1 (meaning329 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [172]) (countLit q [173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_right (literal (valuationOf q) (176)) (literal (valuationOf q) (341)) (countLit q [175]) (countLit q [176]) (count341 q) 1 (meaning176 q) (meaning341 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 341 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning177 q) (meaning343 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 343 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning341 q) (meaning345 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 345 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_two (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 1 (meaning341 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (347)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning339 q) (meaning347 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 347 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 1 (meaning339 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (349)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning335 q) (meaning349 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 349 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 1 (meaning335 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (336)) (literal (valuationOf q) (350)) (countLit q [166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178]) (count349 q) 2 (meaning336 q) (meaning350 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 350 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E107.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112107
