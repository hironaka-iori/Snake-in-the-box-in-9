import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [166, 167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (337)) (countLit q [166, 167, 168, 169]) (countLit q [170, 171, 172, 173]) (count337 q) 1 (meaning329 q) (meaning337 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 337 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (339)) (countLit q [159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning323 q) (meaning339 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 339 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 1 (meaning323 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (341)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 1 (meaning311 q) (meaning341 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 341 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 1 1 (meaning311 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 2 (meaning312 q) (meaning342 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 342 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count343 q) 1 (meaning285 q) (meaning343 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 343 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count343 q) 1 1 (meaning285 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (286)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count343 q) 2 (meaning286 q) (meaning344 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 344 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175, 176])
  have hm := merge_left (literal (valuationOf q) (174)) (literal (valuationOf q) (347)) (countLit q [174]) (countLit q [175, 176]) (count347 q) 1 (meaning174 q) (meaning347 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 347 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (349)) (countLit q [177]) (countLit q [178]) (count349 q) 1 (meaning177 q) (meaning349 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 349 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [177, 178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [177, 178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (353)) (countLit q [177, 178]) (countLit q [179, 180]) (count353 q) 1 (meaning349 q) (meaning353 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 353 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179, 180]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [174, 175, 176]) + (countLit q [177, 178, 179, 180]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176]) (l₂ := [177, 178, 179, 180])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (355)) (countLit q [174, 175, 176]) (countLit q [177, 178, 179, 180]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (357)) (countLit q [182]) (countLit q [183]) (count357 q) 1 (meaning183 q) (meaning357 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 357 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [181]) (countLit q [182, 183]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (359)) (countLit q [181]) (countLit q [182, 183]) (count359 q) 1 (meaning181 q) (meaning359 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 359 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_right (literal (valuationOf q) (185)) (literal (valuationOf q) (361)) (countLit q [184]) (countLit q [185]) (count361 q) 1 (meaning185 q) (meaning361 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 361 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [184, 185]) + (countLit q [186, 187]) := List.countP_append (p := literal q) (l₁ := [184, 185]) (l₂ := [186, 187])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (365)) (countLit q [184, 185]) (countLit q [186, 187]) (count365 q) 1 (meaning361 q) (meaning365 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 365 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [181, 182, 183]) + (countLit q [184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183]) (l₂ := [184, 185, 186, 187])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [181, 182, 183]) (countLit q [184, 185, 186, 187]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [181, 182, 183]) + (countLit q [184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [181, 182, 183]) (l₂ := [184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (367)) (countLit q [181, 182, 183]) (countLit q [184, 185, 186, 187]) (count367 q) 1 (meaning359 q) (meaning367 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 367 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [174, 175, 176, 177, 178, 179, 180]) + (countLit q [181, 182, 183, 184, 185, 186, 187]) := List.countP_append (p := literal q) (l₁ := [174, 175, 176, 177, 178, 179, 180]) (l₂ := [181, 182, 183, 184, 185, 186, 187])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (369)) (countLit q [174, 175, 176, 177, 178, 179, 180]) (countLit q [181, 182, 183, 184, 185, 186, 187]) (count369 q) 1 (meaning355 q) (meaning369 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 369 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [188]) (countLit q [189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_right (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194]) (count377 q) 1 (meaning194 q) (meaning377 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 377 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E257.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112257
