import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (285)) (literal (valuationOf q) (288)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 1 (meaning279 q) (meaning285 q) (meaning288 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 285 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 285 = false ∨ valuation q 288 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (280)) (literal (valuationOf q) (288)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 2 (meaning280 q) (meaning288 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 288 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (288)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning288 q) (meaning290 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 290 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (289)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 (meaning273 q) (meaning289 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 289 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (273)) (literal (valuationOf q) (287)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 1 1 (meaning273 q) (meaning287 q) (meaning290 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 287 = false ∨ valuation q 290 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (274)) (literal (valuationOf q) (290)) (countLit q [133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147]) (count289 q) 2 (meaning274 q) (meaning290 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 290 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 (meaning289 q) (meaning291 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (290)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 2 (meaning290 q) (meaning292 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 292 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (291)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 (meaning261 q) (meaning291 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 291 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (289)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 1 1 (meaning261 q) (meaning289 q) (meaning292 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 289 = false ∨ valuation q 292 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (262)) (literal (valuationOf q) (292)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (count291 q) 2 (meaning262 q) (meaning292 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 292 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning151 q) (meaning297 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 297 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning297 q) (meaning301 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 301 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (305)) (countLit q [156]) (countLit q [157]) (count305 q) 1 (meaning156 q) (meaning305 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 305 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [155]) (countLit q [156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_right (literal (valuationOf q) (161)) (literal (valuationOf q) (311)) (countLit q [160]) (countLit q [161]) (count311 q) 1 (meaning161 q) (meaning311 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 311 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 1 (meaning307 q) (meaning315 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 315 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning303 q) (meaning317 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 317 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (325)) (countLit q [167]) (countLit q [168]) (count325 q) 1 (meaning167 q) (meaning325 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 325 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (327)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 (meaning323 q) (meaning327 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 327 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning321 q) (meaning329 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 329 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E158.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112158
