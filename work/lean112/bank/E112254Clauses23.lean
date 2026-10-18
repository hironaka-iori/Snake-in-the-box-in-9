import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (319)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 (meaning315 q) (meaning319 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 319 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_right (literal (valuationOf q) (165)) (literal (valuationOf q) (321)) (countLit q [164]) (countLit q [165]) (count321 q) 1 (meaning165 q) (meaning321 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 321 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_left (literal (valuationOf q) (164)) (literal (valuationOf q) (321)) (countLit q [164]) (countLit q [165]) (count321 q) 1 (meaning164 q) (meaning321 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 321 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 165 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_two (literal (valuationOf q) (164)) (literal (valuationOf q) (165)) (literal (valuationOf q) (322)) (countLit q [164]) (countLit q [165]) (count321 q) 1 1 (meaning164 q) (meaning165 q) (meaning322 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 165 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 165 = false ∨ valuation q 322 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (325)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 1 (meaning321 q) (meaning325 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 325 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_left (literal (valuationOf q) (322)) (literal (valuationOf q) (326)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 2 (meaning322 q) (meaning326 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 326 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 326 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (326)) (literal (valuationOf q) (328)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 2 (meaning326 q) (meaning328 q) hs
  change valuationOf q 326 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 326 = false ∨ valuation q 328 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (327)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 325 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_two (literal (valuationOf q) (319)) (literal (valuationOf q) (325)) (literal (valuationOf q) (328)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 1 (meaning319 q) (meaning325 q) (meaning328 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 325 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 325 = false ∨ valuation q 328 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (328)) (literal (valuationOf q) (330)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 2 (meaning328 q) (meaning330 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 330 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (313)) (literal (valuationOf q) (329)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 (meaning313 q) (meaning329 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 329 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167]) (count329 q) 1 1 (meaning313 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [168]) (countLit q [170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (333)) (countLit q [168]) (countLit q [170, 171]) (count333 q) 1 (meaning168 q) (meaning333 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 333 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_left (literal (valuationOf q) (174)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning174 q) (meaning337 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 337 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172, 173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [172, 173]) (l₂ := [174, 175])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [172, 173]) (countLit q [174, 175]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [168, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [168, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [168, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (341)) (countLit q [168, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (343)) (countLit q [176]) (countLit q [177]) (count343 q) 1 (meaning176 q) (meaning343 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 343 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (345)) (countLit q [178]) (countLit q [179]) (count345 q) 1 (meaning178 q) (meaning345 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 345 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [176, 177]) (countLit q [178, 179]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [176, 177]) + (countLit q [178, 179]) := List.countP_append (p := literal q) (l₁ := [176, 177]) (l₂ := [178, 179])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (347)) (countLit q [176, 177]) (countLit q [178, 179]) (count347 q) 1 (meaning343 q) (meaning347 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 347 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_right (literal (valuationOf q) (183)) (literal (valuationOf q) (351)) (countLit q [182]) (countLit q [183]) (count351 q) 1 (meaning183 q) (meaning351 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 351 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 182 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [182]) + (countLit q [183]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183])
  have hm := merge_left (literal (valuationOf q) (182)) (literal (valuationOf q) (351)) (countLit q [182]) (countLit q [183]) (count351 q) 1 (meaning182 q) (meaning351 q) hs
  change valuationOf q 182 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 182 = false ∨ valuation q 351 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [180, 181]) (countLit q [182, 183]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [176, 177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (355)) (countLit q [176, 177, 178, 179]) (countLit q [180, 181, 182, 183]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [168, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [168, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E254.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112254
