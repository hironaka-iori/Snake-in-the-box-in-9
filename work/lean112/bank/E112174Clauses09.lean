import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 180 = false := by
  rw [value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (400 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (403 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 183 = false := by
  rw [value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (419 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 184 = false := by
  rw [value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (421 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (436 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 189 = false := by
  rw [value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (439 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 191 = false := by
  rw [value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (443 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (451 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 196 = false := by
  rw [value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (453 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 197 = false := by
  rw [value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (458 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 199 = false := by
  rw [value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (460 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 202 = false := by
  rw [value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 204 = false := by
  rw [value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 205 = false := by
  rw [value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (472 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 207 = false := by
  rw [value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (475 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause304 (q : Nat → Bool) : valuationOf q 107 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [106]) + (countLit q [107]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107])
  have hm := merge_right (literal (valuationOf q) (107)) (literal (valuationOf q) (209)) (countLit q [106]) (countLit q [107]) (count209 q) 1 (meaning107 q) (meaning209 q) hs
  change valuationOf q 107 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 209 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [105]) + (countLit q [106, 107]) := List.countP_append (p := literal q) (l₁ := [105]) (l₂ := [106, 107])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [105]) (countLit q [106, 107]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [109]) + (countLit q [110]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110])
  have hm := merge_right (literal (valuationOf q) (110)) (literal (valuationOf q) (213)) (countLit q [109]) (countLit q [110]) (count213 q) 1 (meaning110 q) (meaning213 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 213 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [108]) + (countLit q [109, 110]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109, 110])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [108]) (countLit q [109, 110]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 108 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [108]) + (countLit q [109, 110]) := List.countP_append (p := literal q) (l₁ := [108]) (l₂ := [109, 110])
  have hm := merge_left (literal (valuationOf q) (108)) (literal (valuationOf q) (215)) (countLit q [108]) (countLit q [109, 110]) (count215 q) 1 (meaning108 q) (meaning215 q) hs
  change valuationOf q 108 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 215 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning215 q) (meaning217 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 217 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning211 q) (meaning217 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 217 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 116 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [115]) + (countLit q [116]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116])
  have hm := merge_right (literal (valuationOf q) (116)) (literal (valuationOf q) (223)) (countLit q [115]) (countLit q [116]) (count223 q) 1 (meaning116 q) (meaning223 q) hs
  change valuationOf q 116 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 223 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (225)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 (meaning223 q) (meaning225 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 225 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 114 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_left (literal (valuationOf q) (114)) (literal (valuationOf q) (225)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 (meaning114 q) (meaning225 q) hs
  change valuationOf q 114 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 225 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 114 = false ∨ valuationOf q 223 = false ∨ valuationOf q 226 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_two (literal (valuationOf q) (114)) (literal (valuationOf q) (223)) (literal (valuationOf q) (226)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 1 (meaning114 q) (meaning223 q) (meaning226 q) hs
  change valuationOf q 114 = false ∨ valuationOf q 223 = false ∨ valuationOf q 226 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 223 = false ∨ valuation q 226 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (228)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 2 (meaning226 q) (meaning228 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 228 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (228)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 2 (meaning228 q) (meaning230 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 230 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning217 q) (meaning229 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 229 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (227)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 1 (meaning217 q) (meaning227 q) (meaning230 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 227 = false ∨ valuation q 230 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E174.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112174
