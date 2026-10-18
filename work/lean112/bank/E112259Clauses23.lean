import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (328)) (literal (valuationOf q) (330)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 2 (meaning328 q) (meaning330 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 330 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_right (literal (valuationOf q) (172)) (literal (valuationOf q) (331)) (countLit q [171]) (countLit q [172]) (count331 q) 1 (meaning172 q) (meaning331 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 331 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuationOf q) (174)) (literal (valuationOf q) (333)) (countLit q [173]) (countLit q [174]) (count333 q) 1 (meaning174 q) (meaning333 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 333 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [171, 172]) (countLit q [173, 174]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (335)) (countLit q [171, 172]) (countLit q [173, 174]) (count335 q) 1 (meaning331 q) (meaning335 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 335 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (337)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 1 (meaning329 q) (meaning337 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 337 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (338)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 2 (meaning330 q) (meaning338 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 338 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [159, 160, 161, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (338)) (literal (valuationOf q) (340)) (countLit q [159, 160, 161, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (339)) (countLit q [159, 160, 161, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 (meaning323 q) (meaning339 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 339 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [159, 160, 161, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 1 (meaning323 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (341)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning311 q) (meaning341 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 341 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 1 (meaning311 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 2 (meaning312 q) (meaning342 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 342 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning285 q) (meaning343 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 343 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 1 (meaning285 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (286)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning286 q) (meaning344 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 344 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_right (literal (valuationOf q) (177)) (literal (valuationOf q) (345)) (countLit q [176]) (countLit q [177]) (count345 q) 1 (meaning177 q) (meaning345 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 345 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [175]) (countLit q [176, 177]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (347)) (countLit q [175]) (countLit q [176, 177]) (count347 q) 1 (meaning175 q) (meaning347 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 347 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_right (literal (valuationOf q) (181)) (literal (valuationOf q) (351)) (countLit q [180]) (countLit q [181]) (count351 q) 1 (meaning181 q) (meaning351 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 351 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178, 179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 181])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [178, 179]) (countLit q [180, 181]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184]) (count357 q) 1 (meaning183 q) (meaning357 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 357 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [182]) (countLit q [183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E259.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112259
