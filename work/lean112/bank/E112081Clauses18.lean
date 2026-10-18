import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 223 = false := by
  rw [value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (486 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (497 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause579 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (235)) (countLit q [119]) (countLit q [120]) (count235 q) 1 (meaning119 q) (meaning235 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 235 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [118]) + (countLit q [119, 120]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119, 120])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [118]) (countLit q [119, 120]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_right (literal (valuationOf q) (122)) (literal (valuationOf q) (239)) (countLit q [121]) (countLit q [122]) (count239 q) 1 (meaning122 q) (meaning239 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 239 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (239)) (countLit q [121]) (countLit q [122]) (count239 q) 1 (meaning121 q) (meaning239 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 239 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 122 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_two (literal (valuationOf q) (121)) (literal (valuationOf q) (122)) (literal (valuationOf q) (240)) (countLit q [121]) (countLit q [122]) (count239 q) 1 1 (meaning121 q) (meaning122 q) (meaning240 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 122 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 122 = false ∨ valuation q 240 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (241)) (countLit q [123]) (countLit q [124]) (count241 q) 1 (meaning123 q) (meaning241 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 241 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (243)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 1 (meaning239 q) (meaning243 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 243 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (literal (valuationOf q) (244)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 1 1 (meaning239 q) (meaning241 q) (meaning244 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = false ∨ valuation q 244 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (244)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 2 (meaning240 q) (meaning244 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 244 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (246)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 2 (meaning244 q) (meaning246 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 246 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (245)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 1 (meaning237 q) (meaning245 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 245 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 243 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_two (literal (valuationOf q) (237)) (literal (valuationOf q) (243)) (literal (valuationOf q) (246)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 1 1 (meaning237 q) (meaning243 q) (meaning246 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 243 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 243 = false ∨ valuation q 246 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning128 q) (meaning251 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 251 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal q) (l₁ := [130]) (l₂ := [131])
  have hm := merge_left (literal (valuationOf q) (130)) (literal (valuationOf q) (253)) (countLit q [130]) (countLit q [131]) (count253 q) 1 (meaning130 q) (meaning253 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 253 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [128, 129]) (countLit q [130, 131]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (255)) (countLit q [128, 129]) (countLit q [130, 131]) (count255 q) 1 (meaning251 q) (meaning255 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 255 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_two (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [128, 129]) (countLit q [130, 131]) (count255 q) 1 1 (meaning251 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (256)) (literal (valuationOf q) (258)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 2 (meaning256 q) (meaning258 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 258 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (258)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 2 (meaning258 q) (meaning260 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 260 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (259)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning245 q) (meaning259 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 259 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 1 (meaning245 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 2 (meaning246 q) (meaning260 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 260 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_right (literal (valuationOf q) (140)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning140 q) (meaning273 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 273 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 139 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuationOf q) (139)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning139 q) (meaning273 q) hs
  change valuationOf q 139 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 273 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (275)) (countLit q [141]) (countLit q [142]) (count275 q) 1 (meaning141 q) (meaning275 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 275 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E081.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112081
