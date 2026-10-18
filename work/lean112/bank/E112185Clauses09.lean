import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (335 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 183 = false := by
  rw [value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (340 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 185 = false := by
  rw [value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (349 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 186 = false := by
  rw [value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (384 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (387 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 189 = false := by
  rw [value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (401 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (427 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (432 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 196 = false := by
  rw [value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (437 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 198 = false := by
  rw [value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (441 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 200 = false := by
  rw [value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (447 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (450 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (462 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 214 = false := by
  rw [value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (473 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 216 = false := by
  rw [value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (479 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause304 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [110]) + (countLit q [111]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111])
  have hm := merge_left (literal (valuationOf q) (110)) (literal (valuationOf q) (217)) (countLit q [110]) (countLit q [111]) (count217 q) 1 (meaning110 q) (meaning217 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 217 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [109]) + (countLit q [110, 111]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110, 111])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (219)) (countLit q [109]) (countLit q [110, 111]) (count219 q) 1 (meaning217 q) (meaning219 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 219 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [109, 110, 111]) + (countLit q [112, 113, 114]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111]) (l₂ := [112, 113, 114])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (225)) (countLit q [109, 110, 111]) (countLit q [112, 113, 114]) (count225 q) 1 (meaning219 q) (meaning225 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 225 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 116 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_left (literal (valuationOf q) (116)) (literal (valuationOf q) (227)) (countLit q [116]) (countLit q [117]) (count227 q) 1 (meaning116 q) (meaning227 q) hs
  change valuationOf q 116 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 227 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [115]) + (countLit q [116, 117]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116, 117])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [115]) (countLit q [116, 117]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [115, 116, 117]) + (countLit q [118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117]) (l₂ := [118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (237)) (countLit q [115, 116, 117]) (countLit q [118, 119, 120, 121]) (count237 q) 1 (meaning229 q) (meaning237 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 237 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [109, 110, 111, 112, 113, 114]) + (countLit q [115, 116, 117, 118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114]) (l₂ := [115, 116, 117, 118, 119, 120, 121])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [109, 110, 111, 112, 113, 114]) (countLit q [115, 116, 117, 118, 119, 120, 121]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [109, 110, 111, 112, 113, 114]) + (countLit q [115, 116, 117, 118, 119, 120, 121]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114]) (l₂ := [115, 116, 117, 118, 119, 120, 121])
  have hm := merge_left (literal (valuationOf q) (225)) (literal (valuationOf q) (239)) (countLit q [109, 110, 111, 112, 113, 114]) (countLit q [115, 116, 117, 118, 119, 120, 121]) (count239 q) 1 (meaning225 q) (meaning239 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 239 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_right (literal (valuationOf q) (124)) (literal (valuationOf q) (241)) (countLit q [123]) (countLit q [124]) (count241 q) 1 (meaning124 q) (meaning241 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 241 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [122]) (countLit q [123, 124]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123, 124])
  have hm := merge_left (literal (valuationOf q) (122)) (literal (valuationOf q) (243)) (countLit q [122]) (countLit q [123, 124]) (count243 q) 1 (meaning122 q) (meaning243 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 243 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [122, 123, 124]) + (countLit q [125, 126, 127]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124]) (l₂ := [125, 126, 127])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (249)) (countLit q [122, 123, 124]) (countLit q [125, 126, 127]) (count249 q) 1 (meaning243 q) (meaning249 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 249 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (263)) (countLit q [122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count263 q) 1 (meaning249 q) (meaning263 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 263 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]) + (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]) (l₂ := [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (265)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]) (countLit q [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 (meaning239 q) (meaning265 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 265 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning136 q) (meaning267 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 267 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136, 137])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [135]) (countLit q [136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E185.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112185
