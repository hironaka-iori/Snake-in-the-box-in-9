import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [118]) + (countLit q [119, 120]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119, 120])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [118]) (countLit q [119, 120]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_right (literal (valuationOf q) (122)) (literal (valuationOf q) (239)) (countLit q [121]) (countLit q [122]) (count239 q) 1 (meaning122 q) (meaning239 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 239 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (239)) (countLit q [121]) (countLit q [122]) (count239 q) 1 (meaning121 q) (meaning239 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 239 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 122 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [121]) + (countLit q [122]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122])
  have hm := merge_two (literal (valuationOf q) (121)) (literal (valuationOf q) (122)) (literal (valuationOf q) (240)) (countLit q [121]) (countLit q [122]) (count239 q) 1 1 (meaning121 q) (meaning122 q) (meaning240 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 122 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 122 = false ∨ valuation q 240 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 241 = true := by
  have hs : count241 q = (countLit q [123]) + (countLit q [124]) := List.countP_append (p := literal q) (l₁ := [123]) (l₂ := [124])
  have hm := merge_left (literal (valuationOf q) (123)) (literal (valuationOf q) (241)) (countLit q [123]) (countLit q [124]) (count241 q) 1 (meaning123 q) (meaning241 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 241 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 241 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 241 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_right (literal (valuationOf q) (241)) (literal (valuationOf q) (243)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 1 (meaning241 q) (meaning243 q) hs
  change valuationOf q 241 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 241 = false ∨ valuation q 243 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_left (literal (valuationOf q) (239)) (literal (valuationOf q) (243)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 1 (meaning239 q) (meaning243 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 243 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_two (literal (valuationOf q) (239)) (literal (valuationOf q) (241)) (literal (valuationOf q) (244)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 1 1 (meaning239 q) (meaning241 q) (meaning244 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 241 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 241 = false ∨ valuation q 244 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 240 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [121, 122]) + (countLit q [123, 124]) := List.countP_append (p := literal q) (l₁ := [121, 122]) (l₂ := [123, 124])
  have hm := merge_left (literal (valuationOf q) (240)) (literal (valuationOf q) (244)) (countLit q [121, 122]) (countLit q [123, 124]) (count243 q) 2 (meaning240 q) (meaning244 q) hs
  change valuationOf q 240 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 244 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (243)) (literal (valuationOf q) (245)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 1 (meaning243 q) (meaning245 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 245 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 244 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_right (literal (valuationOf q) (244)) (literal (valuationOf q) (246)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 2 (meaning244 q) (meaning246 q) hs
  change valuationOf q 244 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 244 = false ∨ valuation q 246 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_left (literal (valuationOf q) (237)) (literal (valuationOf q) (245)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 1 (meaning237 q) (meaning245 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 245 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 243 = false ∨ valuationOf q 246 = true := by
  have hs : count245 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123, 124]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123, 124])
  have hm := merge_two (literal (valuationOf q) (237)) (literal (valuationOf q) (243)) (literal (valuationOf q) (246)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123, 124]) (count245 q) 1 1 (meaning237 q) (meaning243 q) (meaning246 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 243 = false ∨ valuationOf q 246 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 243 = false ∨ valuation q 246 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_right (literal (valuationOf q) (127)) (literal (valuationOf q) (247)) (countLit q [126]) (countLit q [127]) (count247 q) 1 (meaning127 q) (meaning247 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 247 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [125]) (countLit q [126, 127]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning128 q) (meaning251 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 251 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128, 129]) + (countLit q [130, 131]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [130, 131])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (255)) (countLit q [128, 129]) (countLit q [130, 131]) (count255 q) 1 (meaning251 q) (meaning255 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 255 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (249)) (literal (valuationOf q) (257)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 (meaning249 q) (meaning257 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 257 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true := by
  have hs : count257 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (249)) (literal (valuationOf q) (255)) (literal (valuationOf q) (258)) (countLit q [125, 126, 127]) (countLit q [128, 129, 130, 131]) (count257 q) 1 1 (meaning249 q) (meaning255 q) (meaning258 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 255 = false ∨ valuationOf q 258 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 255 = false ∨ valuation q 258 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_right (literal (valuationOf q) (258)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 2 (meaning258 q) (meaning260 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 260 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (259)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 (meaning245 q) (meaning259 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 259 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_two (literal (valuationOf q) (245)) (literal (valuationOf q) (257)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 1 1 (meaning245 q) (meaning257 q) (meaning260 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 257 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 257 = false ∨ valuation q 260 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 246 = false ∨ valuationOf q 260 = true := by
  have hs : count259 q = (countLit q [118, 119, 120, 121, 122, 123, 124]) + (countLit q [125, 126, 127, 128, 129, 130, 131]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120, 121, 122, 123, 124]) (l₂ := [125, 126, 127, 128, 129, 130, 131])
  have hm := merge_left (literal (valuationOf q) (246)) (literal (valuationOf q) (260)) (countLit q [118, 119, 120, 121, 122, 123, 124]) (countLit q [125, 126, 127, 128, 129, 130, 131]) (count259 q) 2 (meaning246 q) (meaning260 q) hs
  change valuationOf q 246 = false ∨ valuationOf q 260 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 246 = false ∨ valuation q 260 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 132 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133, 134])
  have hm := merge_left (literal (valuationOf q) (132)) (literal (valuationOf q) (263)) (countLit q [132]) (countLit q [133, 134]) (count263 q) 1 (meaning132 q) (meaning263 q) hs
  change valuationOf q 132 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 132 = false ∨ valuation q 263 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135, 136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [135, 136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [135, 136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_right (literal (valuationOf q) (269)) (literal (valuationOf q) (271)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_left (literal (valuationOf q) (263)) (literal (valuationOf q) (271)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 1 (meaning263 q) (meaning271 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 271 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true := by
  have hs : count271 q = (countLit q [132, 133, 134]) + (countLit q [135, 136, 137, 138]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134]) (l₂ := [135, 136, 137, 138])
  have hm := merge_two (literal (valuationOf q) (263)) (literal (valuationOf q) (269)) (literal (valuationOf q) (272)) (countLit q [132, 133, 134]) (countLit q [135, 136, 137, 138]) (count271 q) 1 1 (meaning263 q) (meaning269 q) (meaning272 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 269 = false ∨ valuationOf q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E207.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112207
