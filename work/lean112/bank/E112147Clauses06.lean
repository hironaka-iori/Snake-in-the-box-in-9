import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 104 = false ∨ valuationOf q 207 = true := by
  have hs : count207 q = (countLit q [104]) + (countLit q [105, 106]) := List.countP_append (p := literal q) (l₁ := [104]) (l₂ := [105, 106])
  have hm := merge_left (literal (valuationOf q) (104)) (literal (valuationOf q) (207)) (countLit q [104]) (countLit q [105, 106]) (count207 q) 1 (meaning104 q) (meaning207 q) hs
  change valuationOf q 104 = false ∨ valuationOf q 207 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 207 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [101, 102, 103]) + (countLit q [104, 105, 106]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103]) (l₂ := [104, 105, 106])
  have hm := merge_right (literal (valuationOf q) (207)) (literal (valuationOf q) (209)) (countLit q [101, 102, 103]) (countLit q [104, 105, 106]) (count209 q) 1 (meaning207 q) (meaning209 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 209 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [101, 102, 103]) + (countLit q [104, 105, 106]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103]) (l₂ := [104, 105, 106])
  have hm := merge_left (literal (valuationOf q) (203)) (literal (valuationOf q) (209)) (countLit q [101, 102, 103]) (countLit q [104, 105, 106]) (count209 q) 1 (meaning203 q) (meaning209 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 209 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 108 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [108]) + (countLit q [109]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109])
  have hm := merge_left (literal (valuationOf q) (108)) (literal (valuationOf q) (211)) (countLit q [108]) (countLit q [109]) (count211 q) 1 (meaning108 q) (meaning211 q) hs
  change valuationOf q 108 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 211 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [107]) + (countLit q [108, 109]) := List.countP_append (p := literal q) (l₁ := [107]) (l₂ := [108, 109])
  have hm := merge_right (literal (valuationOf q) (211)) (literal (valuationOf q) (213)) (countLit q [107]) (countLit q [108, 109]) (count213 q) 1 (meaning211 q) (meaning213 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 213 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [107, 108, 109]) + (countLit q [110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109]) (l₂ := [110, 111, 112])
  have hm := merge_left (literal (valuationOf q) (213)) (literal (valuationOf q) (219)) (countLit q [107, 108, 109]) (countLit q [110, 111, 112]) (count219 q) 1 (meaning213 q) (meaning219 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 219 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [101, 102, 103, 104, 105, 106]) + (countLit q [107, 108, 109, 110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106]) (l₂ := [107, 108, 109, 110, 111, 112])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [101, 102, 103, 104, 105, 106]) (countLit q [107, 108, 109, 110, 111, 112]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [101, 102, 103, 104, 105, 106]) + (countLit q [107, 108, 109, 110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106]) (l₂ := [107, 108, 109, 110, 111, 112])
  have hm := merge_left (literal (valuationOf q) (209)) (literal (valuationOf q) (221)) (countLit q [101, 102, 103, 104, 105, 106]) (countLit q [107, 108, 109, 110, 111, 112]) (count221 q) 1 (meaning209 q) (meaning221 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 221 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 219 = false ∨ valuationOf q 222 = true := by
  have hs : count221 q = (countLit q [101, 102, 103, 104, 105, 106]) + (countLit q [107, 108, 109, 110, 111, 112]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106]) (l₂ := [107, 108, 109, 110, 111, 112])
  have hm := merge_two (literal (valuationOf q) (209)) (literal (valuationOf q) (219)) (literal (valuationOf q) (222)) (countLit q [101, 102, 103, 104, 105, 106]) (countLit q [107, 108, 109, 110, 111, 112]) (count221 q) 1 1 (meaning209 q) (meaning219 q) (meaning222 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 219 = false ∨ valuationOf q 222 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 219 = false ∨ valuation q 222 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_right (literal (valuationOf q) (124)) (literal (valuationOf q) (237)) (countLit q [123]) (countLit q [124]) (count237 q) 1 (meaning124 q) (meaning237 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 237 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [122]) (countLit q [123, 124]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [113, 114, 115, 116, 117, 118]) + (countLit q [119, 120, 121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [113, 114, 115, 116, 117, 118]) (l₂ := [119, 120, 121, 122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [113, 114, 115, 116, 117, 118]) (countLit q [119, 120, 121, 122, 123, 124]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (245)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (count245 q) 1 (meaning221 q) (meaning245 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 245 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 222 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) + (countLit q [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) (l₂ := [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124])
  have hm := merge_left (literal (valuationOf q) (222)) (literal (valuationOf q) (246)) (countLit q [101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112]) (countLit q [113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]) (count245 q) 2 (meaning222 q) (meaning246 q) hs
  change valuationOf q 222 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 246 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [129]) (countLit q [130]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [128]) (countLit q [129, 130]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_right (literal (valuationOf q) (136)) (literal (valuationOf q) (261)) (countLit q [135]) (countLit q [136]) (count261 q) 1 (meaning136 q) (meaning261 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 261 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135, 136]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (134)) (literal (valuationOf q) (263)) (countLit q [134]) (countLit q [135, 136]) (count263 q) 1 (meaning134 q) (meaning263 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 263 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [131, 132, 133]) + (countLit q [134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133]) (l₂ := [134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [131, 132, 133]) (countLit q [134, 135, 136]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (267)) (countLit q [125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136]) (count267 q) 1 (meaning255 q) (meaning267 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 267 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (269)) (countLit q [138]) (countLit q [139]) (count269 q) 1 (meaning138 q) (meaning269 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 269 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [137]) (countLit q [138, 139]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [141, 142]) (count275 q) 1 (meaning140 q) (meaning275 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 275 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [137, 138, 139]) + (countLit q [140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139]) (l₂ := [140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (277)) (countLit q [137, 138, 139]) (countLit q [140, 141, 142]) (count277 q) 1 (meaning271 q) (meaning277 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 277 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (279)) (countLit q [144]) (countLit q [145]) (count279 q) 1 (meaning144 q) (meaning279 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 279 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [143]) + (countLit q [144, 145]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144, 145])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [143]) (countLit q [144, 145]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E147.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112147
