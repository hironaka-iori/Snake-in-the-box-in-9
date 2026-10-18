import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (307)) (countLit q [155]) (countLit q [156, 157]) (count307 q) 1 (meaning155 q) (meaning307 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 307 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [160]) (count309 q) 1 (meaning160 q) (meaning309 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 309 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [158, 160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (313)) (countLit q [158, 160]) (countLit q [161, 162]) (count313 q) 1 (meaning309 q) (meaning313 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 313 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 160, 161, 162]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 160, 161, 162]) (count315 q) 1 (meaning307 q) (meaning315 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 315 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 160, 161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 160, 161, 162]) (count317 q) 1 (meaning303 q) (meaning317 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 317 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 160, 161, 162])
  have hm := merge_two (literal (valuationOf q) (303)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 160, 161, 162]) (count317 q) 1 1 (meaning303 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_right (literal (valuationOf q) (165)) (literal (valuationOf q) (319)) (countLit q [164]) (countLit q [165]) (count319 q) 1 (meaning165 q) (meaning319 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 319 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_left (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [164]) (countLit q [165]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164, 165])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [163]) (countLit q [164, 165]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_right (literal (valuationOf q) (169)) (literal (valuationOf q) (325)) (countLit q [168]) (countLit q [169]) (count325 q) 1 (meaning169 q) (meaning325 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 325 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [166, 167]) (countLit q [168, 169]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [163, 164, 165]) (countLit q [166, 167, 168, 169]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (329)) (countLit q [163, 164, 165]) (countLit q [166, 167, 168, 169]) (count329 q) 1 (meaning321 q) (meaning329 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 329 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_left (literal (valuationOf q) (172)) (literal (valuationOf q) (333)) (countLit q [172]) (countLit q [173]) (count333 q) 1 (meaning172 q) (meaning333 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 333 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [170, 171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [170, 171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [170, 171]) (countLit q [172, 173]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [170, 171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [170, 171]) (l₂ := [172, 173])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (335)) (countLit q [170, 171]) (countLit q [172, 173]) (count335 q) 1 (meaning331 q) (meaning335 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 335 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning175 q) (meaning337 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 337 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (339)) (countLit q [176]) (countLit q [177]) (count339 q) 1 (meaning176 q) (meaning339 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 339 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [174, 175]) (countLit q [176, 177]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (341)) (countLit q [174, 175]) (countLit q [176, 177]) (count341 q) 1 (meaning337 q) (meaning341 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 341 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [170, 171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [170, 171, 172, 173]) (countLit q [174, 175, 176, 177]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [170, 171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [170, 171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (343)) (countLit q [170, 171, 172, 173]) (countLit q [174, 175, 176, 177]) (count343 q) 1 (meaning335 q) (meaning343 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 343 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [163, 164, 165, 166, 167, 168, 169]) + (countLit q [170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169]) (l₂ := [170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (345)) (countLit q [163, 164, 165, 166, 167, 168, 169]) (countLit q [170, 171, 172, 173, 174, 175, 176, 177]) (count345 q) 1 (meaning329 q) (meaning345 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 345 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 1 (meaning317 q) (meaning347 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 347 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_two (literal (valuationOf q) (317)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 1 1 (meaning317 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (318)) (literal (valuationOf q) (348)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 2 (meaning318 q) (meaning348 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 348 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E104.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112104
