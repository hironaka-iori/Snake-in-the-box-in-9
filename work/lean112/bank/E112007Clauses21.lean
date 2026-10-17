import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 316 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (316)) (literal (valuationOf q) (318)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 2 (meaning316 q) (meaning318 q) hs
  change valuationOf q 316 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 316 = false ∨ valuation q 318 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning303 q) (meaning317 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 317 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_two (literal (valuationOf q) (303)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 1 (meaning303 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (327)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 (meaning323 q) (meaning327 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 327 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning321 q) (meaning329 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 329 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_two (literal (valuationOf q) (321)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 1 (meaning321 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuationOf q) (170)) (literal (valuationOf q) (331)) (countLit q [169]) (countLit q [170]) (count331 q) 1 (meaning170 q) (meaning331 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 331 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (331)) (countLit q [169]) (countLit q [170]) (count331 q) 1 (meaning169 q) (meaning331 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 331 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 170 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_two (literal (valuationOf q) (169)) (literal (valuationOf q) (170)) (literal (valuationOf q) (332)) (countLit q [169]) (countLit q [170]) (count331 q) 1 1 (meaning169 q) (meaning170 q) (meaning332 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 170 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 170 = false ∨ valuation q 332 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_right (literal (valuationOf q) (172)) (literal (valuationOf q) (333)) (countLit q [171]) (countLit q [172]) (count333 q) 1 (meaning172 q) (meaning333 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 333 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (335)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 1 (meaning331 q) (meaning335 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 335 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_two (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 1 1 (meaning331 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 332 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_left (literal (valuationOf q) (332)) (literal (valuationOf q) (336)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 2 (meaning332 q) (meaning336 q) hs
  change valuationOf q 332 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 332 = false ∨ valuation q 336 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (339)) (countLit q [175]) (countLit q [176]) (count339 q) 1 (meaning175 q) (meaning339 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 339 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (341)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 (meaning337 q) (meaning341 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 341 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (343)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 (meaning335 q) (meaning343 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 343 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 1 (meaning335 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (336)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 2 (meaning336 q) (meaning344 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 344 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (344)) (literal (valuationOf q) (346)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 2 (meaning344 q) (meaning346 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 346 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (345)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning329 q) (meaning345 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 345 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 1 (meaning329 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (346)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 2 (meaning330 q) (meaning346 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 346 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E007.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112007
