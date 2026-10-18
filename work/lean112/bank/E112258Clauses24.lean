import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (327)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (320)) (literal (valuationOf q) (328)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 2 (meaning320 q) (meaning328 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 328 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (328)) (literal (valuationOf q) (330)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 2 (meaning328 q) (meaning330 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 330 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (313)) (literal (valuationOf q) (329)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 (meaning313 q) (meaning329 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 329 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 1 (meaning313 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (314)) (literal (valuationOf q) (330)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 2 (meaning314 q) (meaning330 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 330 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning170 q) (meaning331 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 331 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [168]) (countLit q [170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (333)) (countLit q [168]) (countLit q [170, 171]) (count333 q) 1 (meaning168 q) (meaning333 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 333 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning175 q) (meaning337 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 337 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172, 173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [172, 173]) (l₂ := [174, 175])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [172, 173]) (countLit q [174, 175]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [168, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [168, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [168, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (341)) (countLit q [168, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (343)) (countLit q [176]) (countLit q [177]) (count343 q) 1 (meaning176 q) (meaning343 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 343 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_right (literal (valuationOf q) (179)) (literal (valuationOf q) (345)) (countLit q [178]) (countLit q [179]) (count345 q) 1 (meaning179 q) (meaning345 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 345 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (345)) (countLit q [178]) (countLit q [179]) (count345 q) 1 (meaning178 q) (meaning345 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 345 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [176, 177]) (countLit q [178, 179]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (347)) (countLit q [176, 177]) (countLit q [178, 179]) (count347 q) 1 (meaning343 q) (meaning347 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 347 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_right (literal (valuationOf q) (181)) (literal (valuationOf q) (349)) (countLit q [180]) (countLit q [181]) (count349 q) 1 (meaning181 q) (meaning349 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 349 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_left (literal (valuationOf q) (182)) (literal (valuationOf q) (351)) (countLit q [182]) (countLit q [183]) (count351 q) 1 (meaning182 q) (meaning351 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 351 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [180, 181]) (countLit q [182, 183]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (353)) (countLit q [180, 181]) (countLit q [182, 183]) (count353 q) 1 (meaning349 q) (meaning353 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 353 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (355)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_two (literal (valuationOf q) (347)) (literal (valuationOf q) (353)) (literal (valuationOf q) (356)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count355 q) 1 1 (meaning347 q) (meaning353 q) (meaning356 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 353 = false ∨ valuation q 356 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [168, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [168, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 356 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [168, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (356)) (literal (valuationOf q) (358)) (countLit q [168, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (count357 q) 2 (meaning356 q) (meaning358 q) hs
  change valuationOf q 356 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 358 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [168, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (357)) (countLit q [168, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (count357 q) 1 (meaning341 q) (meaning357 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 357 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 355 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [168, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_two (literal (valuationOf q) (341)) (literal (valuationOf q) (355)) (literal (valuationOf q) (358)) (countLit q [168, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (count357 q) 1 1 (meaning341 q) (meaning355 q) (meaning358 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 355 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 355 = false ∨ valuation q 358 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E258.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112258
