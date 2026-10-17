import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (239)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 (meaning233 q) (meaning239 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 239 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_right (literal (valuationOf q) (125)) (literal (valuationOf q) (241)) (countLit q [124]) (countLit q [125]) (count241 q) 1 (meaning125 q) (meaning241 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 241 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (241)) (countLit q [124]) (countLit q [125]) (count241 q) 1 (meaning124 q) (meaning241 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 241 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (245)) (countLit q [126]) (countLit q [127]) (count245 q) 1 (meaning126 q) (meaning245 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 245 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (247)) (countLit q [128]) (countLit q [129]) (count247 q) 1 (meaning128 q) (meaning247 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 247 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (249)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 (meaning245 q) (meaning249 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 249 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = false ∨ valuationOf q 250 = true := by
  have hs : count249 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (literal (valuationOf q) (250)) (countLit q [126, 127]) (countLit q [128, 129]) (count249 q) 1 1 (meaning245 q) (meaning247 q) (meaning250 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = false ∨ valuationOf q 250 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = false ∨ valuation q 250 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 250 = false ∨ valuationOf q 252 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (250)) (literal (valuationOf q) (252)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 2 (meaning250 q) (meaning252 q) hs
  change valuationOf q 250 = false ∨ valuationOf q 252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 250 = false ∨ valuation q 252 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (252)) (literal (valuationOf q) (254)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 2 (meaning252 q) (meaning254 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 254 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 (meaning229 q) (meaning255 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 255 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_two (literal (valuationOf q) (229)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 1 (meaning229 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (230)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 2 (meaning230 q) (meaning256 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 256 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [130]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131, 132])
  have hm := merge_left (literal (valuationOf q) (130)) (literal (valuationOf q) (259)) (countLit q [130]) (countLit q [131, 132]) (count259 q) 1 (meaning130 q) (meaning259 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 259 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (263)) (countLit q [133]) (countLit q [134, 135]) (count263 q) 1 (meaning133 q) (meaning263 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 263 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [130, 131, 132]) + (countLit q [133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132]) (l₂ := [133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (265)) (countLit q [130, 131, 132]) (countLit q [133, 134, 135]) (count265 q) 1 (meaning259 q) (meaning265 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 265 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning136 q) (meaning269 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 269 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning139 q) (meaning271 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 271 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (273)) (countLit q [141]) (countLit q [142]) (count273 q) 1 (meaning141 q) (meaning273 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 273 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [139, 140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [139, 140]) (l₂ := [141, 142])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (275)) (countLit q [139, 140]) (countLit q [141, 142]) (count275 q) 1 (meaning271 q) (meaning275 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 275 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (275)) (literal (valuationOf q) (277)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141, 142]) (count277 q) 1 (meaning275 q) (meaning277 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 277 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E179.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112179
