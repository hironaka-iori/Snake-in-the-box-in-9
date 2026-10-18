import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 172 = false := by
  rw [value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (324 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 175 = false := by
  rw [value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (331 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 177 = false := by
  rw [value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (333 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 179 = false := by
  rw [value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (341 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 180 = false := by
  rw [value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (342 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (345 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 183 = false := by
  rw [value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (346 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 187 = false := by
  rw [value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (419 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 188 = false := by
  rw [value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (421 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (431 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 199 = false := by
  rw [value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (440 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (445 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 206 = false := by
  rw [value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (477 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 210 = false := by
  rw [value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (491 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 211 = false := by
  rw [value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (493 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 216 = false := by
  rw [value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (506 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause241 (q : Nat → Bool) : valuationOf q 110 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [110]) + (countLit q [111, 112]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111, 112])
  have hm := merge_left (literal (valuationOf q) (110)) (literal (valuationOf q) (221)) (countLit q [110]) (countLit q [111, 112]) (count221 q) 1 (meaning110 q) (meaning221 q) hs
  change valuationOf q 110 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 221 = true := counterClause241 (baseVal q)

theorem counterClause242 (q : Nat → Bool) : valuationOf q 115 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [114]) + (countLit q [115]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115])
  have hm := merge_right (literal (valuationOf q) (115)) (literal (valuationOf q) (223)) (countLit q [114]) (countLit q [115]) (count223 q) 1 (meaning115 q) (meaning223 q) hs
  change valuationOf q 115 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 223 = true := counterClause242 (baseVal q)

theorem counterClause243 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [113]) + (countLit q [114, 115]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114, 115])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (225)) (countLit q [113]) (countLit q [114, 115]) (count225 q) 1 (meaning223 q) (meaning225 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 225 = true := counterClause243 (baseVal q)

theorem counterClause244 (q : Nat → Bool) : valuationOf q 113 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [113]) + (countLit q [114, 115]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114, 115])
  have hm := merge_left (literal (valuationOf q) (113)) (literal (valuationOf q) (225)) (countLit q [113]) (countLit q [114, 115]) (count225 q) 1 (meaning113 q) (meaning225 q) hs
  change valuationOf q 113 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 225 = true := counterClause244 (baseVal q)

theorem counterClause245 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause245 (baseVal q)

theorem counterClause246 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause246 (baseVal q)

theorem counterClause247 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true := by
  have hs : count227 q = (countLit q [110, 111, 112]) + (countLit q [113, 114, 115]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112]) (l₂ := [113, 114, 115])
  have hm := merge_two (literal (valuationOf q) (221)) (literal (valuationOf q) (225)) (literal (valuationOf q) (228)) (countLit q [110, 111, 112]) (countLit q [113, 114, 115]) (count227 q) 1 1 (meaning221 q) (meaning225 q) (meaning228 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 225 = false ∨ valuationOf q 228 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 225 = false ∨ valuation q 228 = true := counterClause247 (baseVal q)

theorem counterClause248 (q : Nat → Bool) : valuationOf q 118 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [117]) + (countLit q [118]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118])
  have hm := merge_right (literal (valuationOf q) (118)) (literal (valuationOf q) (229)) (countLit q [117]) (countLit q [118]) (count229 q) 1 (meaning118 q) (meaning229 q) hs
  change valuationOf q 118 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 229 = true := counterClause248 (baseVal q)

theorem counterClause249 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [116]) + (countLit q [117, 118]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117, 118])
  have hm := merge_right (literal (valuationOf q) (229)) (literal (valuationOf q) (231)) (countLit q [116]) (countLit q [117, 118]) (count231 q) 1 (meaning229 q) (meaning231 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 231 = true := counterClause249 (baseVal q)

theorem counterClause250 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [116, 117, 118]) + (countLit q [119, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [116, 117, 118]) (l₂ := [119, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (231)) (literal (valuationOf q) (239)) (countLit q [116, 117, 118]) (countLit q [119, 121, 122, 123]) (count239 q) 1 (meaning231 q) (meaning239 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 239 = true := counterClause250 (baseVal q)

theorem counterClause251 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 121, 122, 123]) (count241 q) 1 (meaning239 q) (meaning241 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = true := counterClause251 (baseVal q)

theorem counterClause252 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (227)) (literal (valuationOf q) (241)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 121, 122, 123]) (count241 q) 1 (meaning227 q) (meaning241 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 241 = true := counterClause252 (baseVal q)

theorem counterClause253 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 242 = true := by
  have hs : count241 q = (countLit q [110, 111, 112, 113, 114, 115]) + (countLit q [116, 117, 118, 119, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115]) (l₂ := [116, 117, 118, 119, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (242)) (countLit q [110, 111, 112, 113, 114, 115]) (countLit q [116, 117, 118, 119, 121, 122, 123]) (count241 q) 2 (meaning228 q) (meaning242 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 242 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 242 = true := counterClause253 (baseVal q)

theorem counterClause254 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (241)) (literal (valuationOf q) (269)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count269 q) 1 (meaning241 q) (meaning269 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 269 = true := counterClause254 (baseVal q)

theorem counterClause255 (q : Nat → Bool) : valuationOf q 242 = false ∨ valuationOf q 270 = true := by
  have hs : count269 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]) + (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]) (l₂ := [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuationOf q) (242)) (literal (valuationOf q) (270)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]) (countLit q [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (count269 q) 2 (meaning242 q) (meaning270 q) hs
  change valuationOf q 242 = false ∨ valuationOf q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 270 = true := counterClause255 (baseVal q)

theorem counterClause256 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [152]) (countLit q [153]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause256 (baseVal q)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E166.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112166
