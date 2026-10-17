import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 182 = false := by
  rw [value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (393 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 193 = false := by
  rw [value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (411 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 194 = false := by
  rw [value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (449 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 197 = false := by
  rw [value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (455 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 198 = false := by
  rw [value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (456 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 199 = false := by
  rw [value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (464 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 201 = false := by
  rw [value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (467 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 204 = false := by
  rw [value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (480 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 208 = false := by
  rw [value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (492 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause170 (q : Nat → Bool) : valuationOf q 106 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [106]) + (countLit q [107]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107])
  have hm := merge_left (literal (valuationOf q) (106)) (literal (valuationOf q) (209)) (countLit q [106]) (countLit q [107]) (count209 q) 1 (meaning106 q) (meaning209 q) hs
  change valuationOf q 106 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 209 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [105]) + (countLit q [106, 107]) := List.countP_append (p := literal q) (l₁ := [105]) (l₂ := [106, 107])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [105]) (countLit q [106, 107]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [105, 106, 107]) + (countLit q [108, 109, 110]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107]) (l₂ := [108, 109, 110])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (217)) (countLit q [105, 106, 107]) (countLit q [108, 109, 110]) (count217 q) 1 (meaning211 q) (meaning217 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 217 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 112 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [112]) + (countLit q [113]) := List.countP_append (p := literal q) (l₁ := [112]) (l₂ := [113])
  have hm := merge_left (literal (valuationOf q) (112)) (literal (valuationOf q) (219)) (countLit q [112]) (countLit q [113]) (count219 q) 1 (meaning112 q) (meaning219 q) hs
  change valuationOf q 112 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 219 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [111]) + (countLit q [112, 113]) := List.countP_append (p := literal q) (l₁ := [111]) (l₂ := [112, 113])
  have hm := merge_right (literal (valuationOf q) (219)) (literal (valuationOf q) (221)) (countLit q [111]) (countLit q [112, 113]) (count221 q) 1 (meaning219 q) (meaning221 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 221 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 115 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [115]) + (countLit q [116]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116])
  have hm := merge_left (literal (valuationOf q) (115)) (literal (valuationOf q) (223)) (countLit q [115]) (countLit q [116]) (count223 q) 1 (meaning115 q) (meaning223 q) hs
  change valuationOf q 115 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 223 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [114]) + (countLit q [115, 116]) := List.countP_append (p := literal q) (l₁ := [114]) (l₂ := [115, 116])
  have hm := merge_right (literal (valuationOf q) (223)) (literal (valuationOf q) (225)) (countLit q [114]) (countLit q [115, 116]) (count225 q) 1 (meaning223 q) (meaning225 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 225 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [111, 112, 113]) + (countLit q [114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [111, 112, 113]) (l₂ := [114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (221)) (literal (valuationOf q) (227)) (countLit q [111, 112, 113]) (countLit q [114, 115, 116]) (count227 q) 1 (meaning221 q) (meaning227 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 227 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_left (literal (valuationOf q) (217)) (literal (valuationOf q) (229)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 (meaning217 q) (meaning229 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 229 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true := by
  have hs : count229 q = (countLit q [105, 106, 107, 108, 109, 110]) + (countLit q [111, 112, 113, 114, 115, 116]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110]) (l₂ := [111, 112, 113, 114, 115, 116])
  have hm := merge_two (literal (valuationOf q) (217)) (literal (valuationOf q) (227)) (literal (valuationOf q) (230)) (countLit q [105, 106, 107, 108, 109, 110]) (countLit q [111, 112, 113, 114, 115, 116]) (count229 q) 1 1 (meaning217 q) (meaning227 q) (meaning230 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 227 = false ∨ valuationOf q 230 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 227 = false ∨ valuation q 230 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [117]) + (countLit q [118, 119]) := List.countP_append (p := literal q) (l₁ := [117]) (l₂ := [118, 119])
  have hm := merge_left (literal (valuationOf q) (117)) (literal (valuationOf q) (233)) (countLit q [117]) (countLit q [118, 119]) (count233 q) 1 (meaning117 q) (meaning233 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 233 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [117, 118, 119]) + (countLit q [120, 121, 122]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119]) (l₂ := [120, 121, 122])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (239)) (countLit q [117, 118, 119]) (countLit q [120, 121, 122]) (count239 q) 1 (meaning233 q) (meaning239 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 239 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (241)) (countLit q [124]) (countLit q [125]) (count241 q) 1 (meaning124 q) (meaning241 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 241 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [123]) (countLit q [124, 125]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [117, 118, 119, 120, 121, 122]) + (countLit q [123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122]) (l₂ := [123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (253)) (countLit q [117, 118, 119, 120, 121, 122]) (countLit q [123, 124, 125, 126, 127, 128, 129]) (count253 q) 1 (meaning239 q) (meaning253 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 253 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (229)) (literal (valuationOf q) (255)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 (meaning229 q) (meaning255 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 255 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_two (literal (valuationOf q) (229)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 1 1 (meaning229 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) + (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (l₂ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129])
  have hm := merge_left (literal (valuationOf q) (230)) (literal (valuationOf q) (256)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]) (count255 q) 2 (meaning230 q) (meaning256 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 256 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (257)) (countLit q [131]) (countLit q [132]) (count257 q) 1 (meaning131 q) (meaning257 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 257 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E225.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112225
