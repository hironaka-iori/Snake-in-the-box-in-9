import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 236 = false := by
  rw [value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (502 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 237 = false := by
  rw [value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (506 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 239 = false := by
  rw [value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (508 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause836 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (243)) (countLit q [121]) (countLit q [122, 123]) (count243 q) 1 (meaning121 q) (meaning243 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 243 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 124 = false ∨ valuationOf q 245 = true := by
  have hs : count245 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal q) (l₁ := [124]) (l₂ := [125])
  have hm := merge_left (literal (valuationOf q) (124)) (literal (valuationOf q) (245)) (countLit q [124]) (countLit q [125]) (count245 q) 1 (meaning124 q) (meaning245 q) hs
  change valuationOf q 124 = false ∨ valuationOf q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 245 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 247 = true := by
  have hs : count247 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal q) (l₁ := [126]) (l₂ := [127])
  have hm := merge_right (literal (valuationOf q) (127)) (literal (valuationOf q) (247)) (countLit q [126]) (countLit q [127]) (count247 q) 1 (meaning127 q) (meaning247 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 247 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [124, 125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [124, 125]) (l₂ := [126, 127])
  have hm := merge_right (literal (valuationOf q) (247)) (literal (valuationOf q) (249)) (countLit q [124, 125]) (countLit q [126, 127]) (count249 q) 1 (meaning247 q) (meaning249 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 249 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 245 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [124, 125]) + (countLit q [126, 127]) := List.countP_append (p := literal q) (l₁ := [124, 125]) (l₂ := [126, 127])
  have hm := merge_left (literal (valuationOf q) (245)) (literal (valuationOf q) (249)) (countLit q [124, 125]) (countLit q [126, 127]) (count249 q) 1 (meaning245 q) (meaning249 q) hs
  change valuationOf q 245 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 249 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [121, 122, 123]) + (countLit q [124, 125, 126, 127]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123]) (l₂ := [124, 125, 126, 127])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [121, 122, 123]) (countLit q [124, 125, 126, 127]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 243 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [121, 122, 123]) + (countLit q [124, 125, 126, 127]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123]) (l₂ := [124, 125, 126, 127])
  have hm := merge_left (literal (valuationOf q) (243)) (literal (valuationOf q) (251)) (countLit q [121, 122, 123]) (countLit q [124, 125, 126, 127]) (count251 q) 1 (meaning243 q) (meaning251 q) hs
  change valuationOf q 243 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 243 = false ∨ valuation q 251 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 130 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_right (literal (valuationOf q) (130)) (literal (valuationOf q) (253)) (countLit q [129]) (countLit q [130]) (count253 q) 1 (meaning130 q) (meaning253 q) hs
  change valuationOf q 130 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 253 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_left (literal (valuationOf q) (129)) (literal (valuationOf q) (253)) (countLit q [129]) (countLit q [130]) (count253 q) 1 (meaning129 q) (meaning253 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 253 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 130 = false ∨ valuationOf q 254 = true := by
  have hs : count253 q = (countLit q [129]) + (countLit q [130]) := List.countP_append (p := literal q) (l₁ := [129]) (l₂ := [130])
  have hm := merge_two (literal (valuationOf q) (129)) (literal (valuationOf q) (130)) (literal (valuationOf q) (254)) (countLit q [129]) (countLit q [130]) (count253 q) 1 1 (meaning129 q) (meaning130 q) (meaning254 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 130 = false ∨ valuationOf q 254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 130 = false ∨ valuation q 254 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (253)) (literal (valuationOf q) (255)) (countLit q [128]) (countLit q [129, 130]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 254 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_right (literal (valuationOf q) (254)) (literal (valuationOf q) (256)) (countLit q [128]) (countLit q [129, 130]) (count255 q) 2 (meaning254 q) (meaning256 q) hs
  change valuationOf q 254 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 254 = false ∨ valuation q 256 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_left (literal (valuationOf q) (128)) (literal (valuationOf q) (255)) (countLit q [128]) (countLit q [129, 130]) (count255 q) 1 (meaning128 q) (meaning255 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 255 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 128 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true := by
  have hs : count255 q = (countLit q [128]) + (countLit q [129, 130]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129, 130])
  have hm := merge_two (literal (valuationOf q) (128)) (literal (valuationOf q) (253)) (literal (valuationOf q) (256)) (countLit q [128]) (countLit q [129, 130]) (count255 q) 1 1 (meaning128 q) (meaning253 q) (meaning256 q) hs
  change valuationOf q 128 = false ∨ valuationOf q 253 = false ∨ valuationOf q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 128 = false ∨ valuation q 253 = false ∨ valuation q 256 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (257)) (countLit q [131]) (countLit q [132]) (count257 q) 1 (meaning131 q) (meaning257 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 257 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 134 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_right (literal (valuationOf q) (134)) (literal (valuationOf q) (259)) (countLit q [133]) (countLit q [134]) (count259 q) 1 (meaning134 q) (meaning259 q) hs
  change valuationOf q 134 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 134 = false ∨ valuation q 259 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_right (literal (valuationOf q) (259)) (literal (valuationOf q) (261)) (countLit q [131, 132]) (countLit q [133, 134]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [131, 132]) + (countLit q [133, 134]) := List.countP_append (p := literal q) (l₁ := [131, 132]) (l₂ := [133, 134])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (261)) (countLit q [131, 132]) (countLit q [133, 134]) (count261 q) 1 (meaning257 q) (meaning261 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 261 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (261)) (literal (valuationOf q) (263)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 1 (meaning261 q) (meaning263 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 263 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (263)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 1 (meaning255 q) (meaning263 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 263 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (261)) (literal (valuationOf q) (264)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 1 1 (meaning255 q) (meaning261 q) (meaning264 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 261 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 261 = false ∨ valuation q 264 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 264 = true := by
  have hs : count263 q = (countLit q [128, 129, 130]) + (countLit q [131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130]) (l₂ := [131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (256)) (literal (valuationOf q) (264)) (countLit q [128, 129, 130]) (countLit q [131, 132, 133, 134]) (count263 q) 2 (meaning256 q) (meaning264 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 264 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 264 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 264 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_right (literal (valuationOf q) (264)) (literal (valuationOf q) (266)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 2 (meaning264 q) (meaning266 q) hs
  change valuationOf q 264 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 264 = false ∨ valuation q 266 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_left (literal (valuationOf q) (251)) (literal (valuationOf q) (265)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 (meaning251 q) (meaning265 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 265 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true := by
  have hs : count265 q = (countLit q [121, 122, 123, 124, 125, 126, 127]) + (countLit q [128, 129, 130, 131, 132, 133, 134]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127]) (l₂ := [128, 129, 130, 131, 132, 133, 134])
  have hm := merge_two (literal (valuationOf q) (251)) (literal (valuationOf q) (263)) (literal (valuationOf q) (266)) (countLit q [121, 122, 123, 124, 125, 126, 127]) (countLit q [128, 129, 130, 131, 132, 133, 134]) (count265 q) 1 1 (meaning251 q) (meaning263 q) (meaning266 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 263 = false ∨ valuationOf q 266 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 263 = false ∨ valuation q 266 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 137 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_right (literal (valuationOf q) (137)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning137 q) (meaning267 q) hs
  change valuationOf q 137 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 137 = false ∨ valuation q 267 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuationOf q) (136)) (literal (valuationOf q) (267)) (countLit q [136]) (countLit q [137]) (count267 q) 1 (meaning136 q) (meaning267 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 267 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [135]) + (countLit q [136, 137]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136, 137])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [135]) (countLit q [136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E004.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112004
