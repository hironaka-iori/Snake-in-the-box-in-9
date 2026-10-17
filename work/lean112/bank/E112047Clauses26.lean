import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_two (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 1 1 (meaning331 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 332 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_left (literal (valuationOf q) (332)) (literal (valuationOf q) (336)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 2 (meaning332 q) (meaning336 q) hs
  change valuationOf q 332 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 332 = false ∨ valuation q 336 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuationOf q) (174)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning174 q) (meaning337 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 337 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_right (literal (valuationOf q) (176)) (literal (valuationOf q) (339)) (countLit q [175]) (countLit q [176]) (count339 q) 1 (meaning176 q) (meaning339 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 339 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (341)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 (meaning337 q) (meaning341 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 341 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_two (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 1 (meaning337 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (343)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 (meaning335 q) (meaning343 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 343 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 1 (meaning335 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (336)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 2 (meaning336 q) (meaning344 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 344 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (344)) (literal (valuationOf q) (346)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 2 (meaning344 q) (meaning346 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 346 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (345)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning329 q) (meaning345 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 345 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 1 (meaning329 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning317 q) (meaning347 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 347 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (317)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 1 (meaning317 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (318)) (literal (valuationOf q) (348)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 2 (meaning318 q) (meaning348 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 348 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 1 (meaning291 q) (meaning349 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 349 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (291)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 1 1 (meaning291 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (292)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 2 (meaning292 q) (meaning350 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 350 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [178]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [180])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (351)) (countLit q [178]) (countLit q [180]) (count351 q) 1 (meaning178 q) (meaning351 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 351 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [177]) + (countLit q [178, 180]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178, 180])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [177]) (countLit q [178, 180]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (355)) (countLit q [181]) (countLit q [182]) (count355 q) 1 (meaning181 q) (meaning355 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 355 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_right (literal (valuationOf q) (184)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184]) (count357 q) 1 (meaning184 q) (meaning357 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 357 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [181, 182]) (countLit q [183, 184]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E047.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112047
