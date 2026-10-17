import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause129 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123])
  have hm := merge_two (literal (valuationOf q) (233)) (literal (valuationOf q) (237)) (literal (valuationOf q) (240)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123]) (count239 q) 1 1 (meaning233 q) (meaning237 q) (meaning240 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 237 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 237 = false ∨ valuation q 240 = true := counterClause129 (baseVal q)

theorem counterClause130 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [118, 119, 120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [118, 119, 120, 121, 122, 123]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause130 (baseVal q)

theorem counterClause131 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [118, 119, 120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (240)) (literal (valuationOf q) (242)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [118, 119, 120, 121, 122, 123]) (count241 q) 2 (meaning240 q) (meaning242 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 242 = true := counterClause131 (baseVal q)

theorem counterClause132 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [118, 119, 120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (241)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [118, 119, 120, 121, 122, 123]) (count241 q) 1 (meaning229 q) (meaning241 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 241 = true := counterClause132 (baseVal q)

theorem counterClause133 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 239 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [112, 113, 114, 115, 116, 117]) + (countLit q [118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117]) (l₂ := [118, 119, 120, 121, 122, 123])
  have hm := merge_two (literal (valuationOf q) (229)) (literal (valuationOf q) (239)) (literal (valuationOf q) (242)) (countLit q [112, 113, 114, 115, 116, 117]) (countLit q [118, 119, 120, 121, 122, 123]) (count241 q) 1 1 (meaning229 q) (meaning239 q) (meaning242 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 239 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 239 = false ∨ valuation q 242 = true := counterClause133 (baseVal q)

theorem counterClause134 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause134 (baseVal q)

theorem counterClause135 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (242)) (literal (valuationOf q) (244)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (count243 q) 2 (meaning242 q) (meaning244 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 244 = true := counterClause135 (baseVal q)

theorem counterClause136 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (220)) (literal (valuationOf q) (244)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (count243 q) 2 (meaning220 q) (meaning244 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 244 = true := counterClause136 (baseVal q)

theorem counterClause137 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_right (literal (valuationOf q) (132)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning132 q) (meaning255 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 255 = true := counterClause137 (baseVal q)

theorem counterClause138 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause138 (baseVal q)

theorem counterClause139 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 132 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_two (literal (valuationOf q) (131)) (literal (valuationOf q) (132)) (literal (valuationOf q) (256)) (countLit q [131]) (countLit q [132]) (count255 q) 1 1 (meaning131 q) (meaning132 q) (meaning256 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 132 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 132 = false ∨ valuation q 256 = true := counterClause139 (baseVal q)

theorem counterClause140 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [130]) (countLit q [131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause140 (baseVal q)

theorem counterClause141 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (256)) (literal (valuationOf q) (258)) (countLit q [130]) (countLit q [131, 132]) (count257 q) 2 (meaning256 q) (meaning258 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 258 = true := counterClause141 (baseVal q)

theorem counterClause142 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134, 135]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause142 (baseVal q)

theorem counterClause143 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause143 (baseVal q)

theorem counterClause144 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (263)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count263 q) 1 (meaning257 q) (meaning263 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 263 = true := counterClause144 (baseVal q)

theorem counterClause145 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (261)) (literal (valuationOf q) (264)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count263 q) 1 1 (meaning257 q) (meaning261 q) (meaning264 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 261 = false ∨ valuation q 264 = true := counterClause145 (baseVal q)

theorem counterClause146 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (258)) (literal (valuationOf q) (264)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count263 q) 2 (meaning258 q) (meaning264 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 264 = true := counterClause146 (baseVal q)

theorem counterClause147 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause147 (baseVal q)

theorem counterClause148 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (264)) (literal (valuationOf q) (266)) (countLit q [124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135]) (count265 q) 2 (meaning264 q) (meaning266 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 266 = true := counterClause148 (baseVal q)

theorem counterClause149 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause149 (baseVal q)

theorem counterClause150 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause150 (baseVal q)

theorem counterClause151 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning136 q) (meaning269 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 269 = true := counterClause151 (baseVal q)

theorem counterClause152 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (271)) (countLit q [140]) (countLit q [141]) (count271 q) 1 (meaning140 q) (meaning271 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 271 = true := counterClause152 (baseVal q)

theorem counterClause153 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140, 141])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140, 141]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause153 (baseVal q)

theorem counterClause154 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (275)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141]) (count275 q) 1 (meaning269 q) (meaning275 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 275 = true := counterClause154 (baseVal q)

theorem counterClause155 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141]) (count275 q) 1 1 (meaning269 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause155 (baseVal q)

theorem counterClause156 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (277)) (countLit q [143]) (countLit q [144]) (count277 q) 1 (meaning143 q) (meaning277 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 277 = true := counterClause156 (baseVal q)

theorem counterClause157 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [142]) (countLit q [143, 144]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause157 (baseVal q)

theorem counterClause158 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [142, 143, 144]) + (countLit q [145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [142, 143, 144]) (l₂ := [145, 146, 147, 148])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [142, 143, 144]) (countLit q [145, 146, 147, 148]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause158 (baseVal q)

theorem counterClause159 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause159 (baseVal q)

theorem counterClause160 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true := by
  have hs : count289 q = (countLit q [136, 137, 138, 139, 140, 141]) + (countLit q [142, 143, 144, 145, 146, 147, 148]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141]) (l₂ := [142, 143, 144, 145, 146, 147, 148])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (287)) (literal (valuationOf q) (290)) (countLit q [136, 137, 138, 139, 140, 141]) (countLit q [142, 143, 144, 145, 146, 147, 148]) (count289 q) 1 1 (meaning275 q) (meaning287 q) (meaning290 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 287 = false ∨ valuationOf q 290 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 287 = false ∨ valuation q 290 = true := counterClause160 (baseVal q)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E149.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112149
