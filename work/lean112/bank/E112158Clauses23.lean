import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (258)) (literal (valuationOf q) (260)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 2 (meaning258 q) (meaning260 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 260 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (251)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 1 1 (meaning251 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [126, 127, 128]) + (countLit q [129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [126, 127, 128]) (l₂ := [129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (252)) (literal (valuationOf q) (260)) (countLit q [126, 127, 128]) (countLit q [129, 130, 131, 132]) (count259 q) 2 (meaning252 q) (meaning260 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 260 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 260 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_right (literal (valuationOf q) (260)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 2 (meaning260 q) (meaning262 q) hs
  change valuationOf q 260 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 260 = false ∨ valuation q 262 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (261)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 (meaning247 q) (meaning261 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 261 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_two (literal (valuationOf q) (247)) (literal (valuationOf q) (259)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 1 1 (meaning247 q) (meaning259 q) (meaning262 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 259 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 259 = false ∨ valuation q 262 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 262 = true := by
  have hs : count261 q = (countLit q [119, 120, 121, 122, 123, 124, 125]) + (countLit q [126, 127, 128, 129, 130, 131, 132]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125]) (l₂ := [126, 127, 128, 129, 130, 131, 132])
  have hm := merge_left (literal (valuationOf q) (248)) (literal (valuationOf q) (262)) (countLit q [119, 120, 121, 122, 123, 124, 125]) (countLit q [126, 127, 128, 129, 130, 131, 132]) (count261 q) 2 (meaning248 q) (meaning262 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 262 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 262 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135]) (count263 q) 1 (meaning134 q) (meaning263 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 263 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (265)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 (meaning133 q) (meaning265 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 265 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_two (literal (valuationOf q) (133)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [133]) (countLit q [134, 135]) (count265 q) 1 1 (meaning133 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning136 q) (meaning267 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 267 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [136, 137]) (countLit q [138, 139]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 1 (meaning265 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (274)) (countLit q [133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 2 (meaning266 q) (meaning274 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 274 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [141]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [141]) (count275 q) 1 (meaning140 q) (meaning275 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 275 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 141 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_two (literal (valuationOf q) (140)) (literal (valuationOf q) (141)) (literal (valuationOf q) (276)) (countLit q [140]) (countLit q [141]) (count275 q) 1 1 (meaning140 q) (meaning141 q) (meaning276 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 141 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 141 = false ∨ valuation q 276 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 280 = true := by
  have hs : count279 q = (countLit q [140, 141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [140, 141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (280)) (countLit q [140, 141]) (countLit q [142, 143]) (count279 q) 2 (meaning276 q) (meaning280 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 280 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 280 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_right (literal (valuationOf q) (145)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning145 q) (meaning281 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 281 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning144 q) (meaning281 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 281 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning147 q) (meaning283 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 283 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (literal (valuationOf q) (286)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 1 (meaning281 q) (meaning283 q) (meaning286 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = false ∨ valuation q 286 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [140, 141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (286)) (literal (valuationOf q) (288)) (countLit q [140, 141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 2 (meaning286 q) (meaning288 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 288 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E158.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112158
