import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (286)) (literal (valuationOf q) (288)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 2 (meaning286 q) (meaning288 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 288 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (285)) (literal (valuationOf q) (288)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 1 (meaning279 q) (meaning285 q) (meaning288 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 285 = false ∨ valuation q 288 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (288)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning288 q) (meaning290 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 290 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (289)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning273 q) (meaning289 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 289 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (273)) (literal (valuationOf q) (287)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 1 (meaning273 q) (meaning287 q) (meaning290 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 287 = false ∨ valuation q 290 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (274)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning274 q) (meaning290 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 290 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (290)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 2 (meaning290 q) (meaning292 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 292 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (291)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 (meaning261 q) (meaning291 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 291 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (289)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 1 (meaning261 q) (meaning289 q) (meaning292 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 289 = false ∨ valuation q 292 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (293)) (countLit q [149]) (countLit q [150]) (count293 q) 1 (meaning149 q) (meaning293 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 293 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [148]) (countLit q [149, 150]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning152 q) (meaning297 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 297 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning297 q) (meaning301 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 301 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (303)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 (meaning295 q) (meaning303 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 303 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (307)) (countLit q [155]) (countLit q [156, 157]) (count307 q) 1 (meaning155 q) (meaning307 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 307 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning158 q) (meaning309 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 309 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_right (literal (valuationOf q) (161)) (literal (valuationOf q) (311)) (countLit q [160]) (countLit q [161]) (count311 q) 1 (meaning161 q) (meaning311 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 311 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (311)) (countLit q [160]) (countLit q [161]) (count311 q) 1 (meaning160 q) (meaning311 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 311 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (313)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 (meaning309 q) (meaning313 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 313 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_two (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 1 (meaning309 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (314)) (literal (valuationOf q) (316)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 2 (meaning314 q) (meaning316 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 316 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 1 (meaning307 q) (meaning315 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 315 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E007.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112007
