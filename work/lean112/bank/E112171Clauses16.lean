import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (307)) (countLit q [144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157]) (count307 q) 1 (meaning293 q) (meaning307 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 307 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157]) (count307 q) 1 1 (meaning293 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (308)) (countLit q [144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157]) (count307 q) 2 (meaning294 q) (meaning308 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 308 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159, 160])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (311)) (countLit q [158]) (countLit q [159, 160]) (count311 q) 1 (meaning158 q) (meaning311 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 311 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_right (literal (valuationOf q) (162)) (literal (valuationOf q) (313)) (countLit q [161]) (countLit q [162]) (count313 q) 1 (meaning162 q) (meaning313 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 313 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (315)) (countLit q [163]) (countLit q [164]) (count315 q) 1 (meaning163 q) (meaning315 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 315 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [161, 162]) (countLit q [163, 164]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_left (literal (valuationOf q) (313)) (literal (valuationOf q) (317)) (countLit q [161, 162]) (countLit q [163, 164]) (count317 q) 1 (meaning313 q) (meaning317 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 317 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163, 164])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163, 164]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163, 164]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163, 164])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (319)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163, 164]) (count319 q) 1 (meaning311 q) (meaning319 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 319 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (321)) (countLit q [166]) (countLit q [167]) (count321 q) 1 (meaning166 q) (meaning321 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 321 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166, 167]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (325)) (countLit q [168]) (countLit q [169]) (count325 q) 1 (meaning168 q) (meaning325 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 325 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (327)) (countLit q [170]) (countLit q [171]) (count327 q) 1 (meaning171 q) (meaning327 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 327 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (327)) (countLit q [170]) (countLit q [171]) (count327 q) 1 (meaning170 q) (meaning327 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 327 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [168, 169]) (countLit q [170, 171]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [168, 169]) (countLit q [170, 171]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [165, 166, 167]) + (countLit q [168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167]) (l₂ := [168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [165, 166, 167]) (countLit q [168, 169, 170, 171]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [165, 166, 167]) + (countLit q [168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167]) (l₂ := [168, 169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [165, 166, 167]) (countLit q [168, 169, 170, 171]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (333)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171]) (count333 q) 1 (meaning319 q) (meaning333 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 333 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 331 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171])
  have hm := merge_two (literal (valuationOf q) (319)) (literal (valuationOf q) (331)) (literal (valuationOf q) (334)) (countLit q [158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171]) (count333 q) 1 1 (meaning319 q) (meaning331 q) (meaning334 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 331 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 331 = false ∨ valuation q 334 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 334 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (334)) (literal (valuationOf q) (336)) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count335 q) 2 (meaning334 q) (meaning336 q) hs
  change valuationOf q 334 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 334 = false ∨ valuation q 336 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (335)) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count335 q) 1 (meaning307 q) (meaning335 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 335 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count335 q) 1 1 (meaning307 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (336)) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count335 q) 2 (meaning308 q) (meaning336 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 336 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_right (literal (valuationOf q) (336)) (literal (valuationOf q) (338)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count337 q) 2 (meaning336 q) (meaning338 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 338 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (337)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]) (count337 q) 1 (meaning281 q) (meaning337 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 337 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E171.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112171
