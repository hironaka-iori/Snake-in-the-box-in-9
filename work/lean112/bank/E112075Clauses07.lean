import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause225 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (227)) (countLit q [117]) (countLit q [118]) (count227 q) 1 (meaning117 q) (meaning227 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 227 = true := counterClause225 (baseVal q)

theorem counterClause226 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [115, 116]) + (countLit q [117, 118]) := List.countP_append (p := literal q) (l₁ := [115, 116]) (l₂ := [117, 118])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [115, 116]) (countLit q [117, 118]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause226 (baseVal q)

theorem counterClause227 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [115, 116]) + (countLit q [117, 118]) := List.countP_append (p := literal q) (l₁ := [115, 116]) (l₂ := [117, 118])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (229)) (countLit q [115, 116]) (countLit q [117, 118]) (count229 q) 1 (meaning225 q) (meaning229 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 229 = true := counterClause227 (baseVal q)

theorem counterClause228 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117, 118]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117, 118])
  have hm := merge_right (literal (valuationOf q) (229)) (literal (valuationOf q) (231)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117, 118]) (count231 q) 1 (meaning229 q) (meaning231 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 231 = true := counterClause228 (baseVal q)

theorem counterClause229 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117, 118]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117, 118])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (231)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117, 118]) (count231 q) 1 (meaning223 q) (meaning231 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 231 = true := counterClause229 (baseVal q)

theorem counterClause230 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause230 (baseVal q)

theorem counterClause231 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (233)) (countLit q [106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118]) (count233 q) 1 (meaning219 q) (meaning233 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 233 = true := counterClause231 (baseVal q)

theorem counterClause232 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [120]) + (countLit q [121]) := List.countP_append (p := literal q) (l₁ := [120]) (l₂ := [121])
  have hm := merge_right (literal (valuationOf q) (121)) (literal (valuationOf q) (235)) (countLit q [120]) (countLit q [121]) (count235 q) 1 (meaning121 q) (meaning235 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 235 = true := counterClause232 (baseVal q)

theorem counterClause233 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [119]) + (countLit q [120, 121]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120, 121])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [119]) (countLit q [120, 121]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause233 (baseVal q)

theorem counterClause234 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [119, 120, 121]) + (countLit q [122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121]) (l₂ := [122, 123, 124])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (243)) (countLit q [119, 120, 121]) (countLit q [122, 123, 124]) (count243 q) 1 (meaning237 q) (meaning243 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 243 = true := counterClause234 (baseVal q)

theorem counterClause235 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (257)) (countLit q [119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count257 q) 1 (meaning243 q) (meaning257 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 257 = true := counterClause235 (baseVal q)

theorem counterClause236 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]) + (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]) (l₂ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause236 (baseVal q)

theorem counterClause237 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]) + (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]) (l₂ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (259)) (countLit q [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118]) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning233 q) (meaning259 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 259 = true := counterClause237 (baseVal q)

theorem counterClause238 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning140 q) (meaning271 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 271 = true := counterClause238 (baseVal q)

theorem counterClause239 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (271)) (countLit q [139]) (countLit q [140]) (count271 q) 1 (meaning139 q) (meaning271 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 271 = true := counterClause239 (baseVal q)

theorem counterClause240 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [138]) (countLit q [139, 140]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause240 (baseVal q)

theorem counterClause241 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [141]) (countLit q [142]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 143 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal q) (l₁ := [143]) (l₂ := [144])
  have hm := merge_left (literal (valuationOf q) (143)) (literal (valuationOf q) (277)) (countLit q [143]) (countLit q [144]) (count277 q) 1 (meaning143 q) (meaning277 q) hs
  change valuationOf q 143 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 143 = false ∨ valuation q 277 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [141, 142]) (countLit q [143, 144]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [141, 142]) (countLit q [143, 144]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (281)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count281 q) 1 (meaning273 q) (meaning281 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 281 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (285)) (countLit q [146]) (countLit q [147]) (count285 q) 1 (meaning147 q) (meaning285 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 285 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (285)) (countLit q [146]) (countLit q [147]) (count285 q) 1 (meaning146 q) (meaning285 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 285 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [145]) (countLit q [146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (293)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150]) (count293 q) 1 (meaning287 q) (meaning293 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 293 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [154]) (countLit q [155]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [154, 155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [154, 155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [154, 155]) (countLit q [156, 157]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [151, 152, 153]) + (countLit q [154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153]) (l₂ := [154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [151, 152, 153]) (countLit q [154, 155, 156, 157]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (307)) (countLit q [145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157]) (count307 q) 1 (meaning293 q) (meaning307 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 307 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E075.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112075
