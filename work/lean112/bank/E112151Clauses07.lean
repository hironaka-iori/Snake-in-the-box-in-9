import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 109 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [109]) + (countLit q [110]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110])
  have hm := merge_left (literal (valuationOf q) (109)) (literal (valuationOf q) (215)) (countLit q [109]) (countLit q [110]) (count215 q) 1 (meaning109 q) (meaning215 q) hs
  change valuationOf q 109 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 215 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [108]) + (countLit q [109, 110]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109, 110])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (217)) (countLit q [108]) (countLit q [109, 110]) (count217 q) 1 (meaning215 q) (meaning217 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 217 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 113 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [112]) + (countLit q [113]) := List.countP_append (p := literal q) (l₁ := [112]) (l₂ := [113])
  have hm := merge_right (literal (valuationOf q) (113)) (literal (valuationOf q) (219)) (countLit q [112]) (countLit q [113]) (count219 q) 1 (meaning113 q) (meaning219 q) hs
  change valuationOf q 113 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 219 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [108, 109, 110]) + (countLit q [111, 112, 113]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110]) (l₂ := [111, 112, 113])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (223)) (countLit q [108, 109, 110]) (countLit q [111, 112, 113]) (count223 q) 1 (meaning217 q) (meaning223 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 223 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 221 = false ∨ valuationOf q 224 = true := by
  have hs : count223 q = (countLit q [108, 109, 110]) + (countLit q [111, 112, 113]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110]) (l₂ := [111, 112, 113])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (221)) (literal (valuationOf q) (224)) (countLit q [108, 109, 110]) (countLit q [111, 112, 113]) (count223 q) 1 1 (meaning217 q) (meaning221 q) (meaning224 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 221 = false ∨ valuationOf q 224 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 221 = false ∨ valuation q 224 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 115 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [115]) + (countLit q [116, 117]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116, 117])
  have hm := merge_left (literal (valuationOf q) (115)) (literal (valuationOf q) (227)) (countLit q [115]) (countLit q [116, 117]) (count227 q) 1 (meaning115 q) (meaning227 q) hs
  change valuationOf q 115 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 227 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_right (literal (valuationOf q) (119)) (literal (valuationOf q) (229)) (countLit q [118]) (countLit q [119]) (count229 q) 1 (meaning119 q) (meaning229 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 229 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [118]) + (countLit q [119]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119])
  have hm := merge_left (literal (valuationOf q) (118)) (literal (valuationOf q) (229)) (countLit q [118]) (countLit q [119]) (count229 q) 1 (meaning118 q) (meaning229 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 229 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [118, 119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [118, 119]) (l₂ := [120, 121])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (233)) (countLit q [118, 119]) (countLit q [120, 121]) (count233 q) 1 (meaning229 q) (meaning233 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 233 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (235)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count235 q) 1 (meaning233 q) (meaning235 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 235 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (235)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count235 q) 1 (meaning227 q) (meaning235 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 235 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [108, 109, 110, 111, 112, 113]) + (countLit q [115, 116, 117, 118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113]) (l₂ := [115, 116, 117, 118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [108, 109, 110, 111, 112, 113]) (countLit q [115, 116, 117, 118, 119, 120, 121]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [108, 109, 110, 111, 112, 113]) + (countLit q [115, 116, 117, 118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113]) (l₂ := [115, 116, 117, 118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (237)) (countLit q [108, 109, 110, 111, 112, 113]) (countLit q [115, 116, 117, 118, 119, 120, 121]) (count237 q) 1 (meaning223 q) (meaning237 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 237 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 235 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [108, 109, 110, 111, 112, 113]) + (countLit q [115, 116, 117, 118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113]) (l₂ := [115, 116, 117, 118, 119, 120, 121])
  have hm := merge_two (literal (valuationOf q) (223)) (literal (valuationOf q) (235)) (literal (valuationOf q) (238)) (countLit q [108, 109, 110, 111, 112, 113]) (countLit q [115, 116, 117, 118, 119, 120, 121]) (count237 q) 1 1 (meaning223 q) (meaning235 q) (meaning238 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 235 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 235 = false ∨ valuation q 238 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 224 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [108, 109, 110, 111, 112, 113]) + (countLit q [115, 116, 117, 118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113]) (l₂ := [115, 116, 117, 118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (224)) (literal (valuationOf q) (238)) (countLit q [108, 109, 110, 111, 112, 113]) (countLit q [115, 116, 117, 118, 119, 120, 121]) (count237 q) 2 (meaning224 q) (meaning238 q) hs
  change valuationOf q 224 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 224 = false ∨ valuation q 238 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 126 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_left (literal (valuationOf q) (126)) (literal (valuationOf q) (243)) (countLit q [126]) (countLit q [127]) (count243 q) 1 (meaning126 q) (meaning243 q) hs
  change valuationOf q 126 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 126 = false ∨ valuation q 243 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [125]) (countLit q [126, 127]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 125 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_left (literal (valuationOf q) (125)) (literal (valuationOf q) (245)) (countLit q [125]) (countLit q [126, 127]) (count245 q) 1 (meaning125 q) (meaning245 q) hs
  change valuationOf q 125 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 245 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127])
  have hm := merge_right (literal (valuationOf q) (245)) (literal (valuationOf q) (247)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129, 130]) (count251 q) 1 (meaning128 q) (meaning251 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 251 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (255)) (countLit q [133]) (countLit q [134]) (count255 q) 1 (meaning133 q) (meaning255 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 255 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [131, 132]) (countLit q [133, 134]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (259)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count259 q) 1 (meaning251 q) (meaning259 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 259 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (261)) (countLit q [122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count261 q) 1 (meaning247 q) (meaning261 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 261 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (263)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (count263 q) 1 (meaning237 q) (meaning263 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 263 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134])
  have hm := merge_two (literal (valuationOf q) (237)) (literal (valuationOf q) (261)) (literal (valuationOf q) (264)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (count263 q) 1 1 (meaning237 q) (meaning261 q) (meaning264 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 261 = false ∨ valuation q 264 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (238)) (literal (valuationOf q) (264)) (countLit q [108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (count263 q) 2 (meaning238 q) (meaning264 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 264 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_right (literal (valuationOf q) (159)) (literal (valuationOf q) (305)) (countLit q [158]) (countLit q [159]) (count305 q) 1 (meaning159 q) (meaning305 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 305 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E151.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112151
