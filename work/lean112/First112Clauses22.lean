import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 210 = false := by
  rw [value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (426 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 212 = false := by
  rw [value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (428 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 214 = false := by
  rw [value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (431 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 215 = false := by
  rw [value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (433 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 217 = false := by
  rw [value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (436 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 219 = false := by
  rw [value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (439 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 220 = false := by
  rw [value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (440 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 223 = false := by
  rw [value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (443 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 226 = false := by
  rw [value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (481 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 227 = false := by
  rw [value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (482 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 231 = false := by
  rw [value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (488 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 232 = false := by
  rw [value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (491 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 233 = false := by
  rw [value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (493 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 235 = false := by
  rw [value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (496 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (499 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 239 = false := by
  rw [value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (502 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 241 = false := by
  rw [value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (508 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 244 = false := by
  rw [value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (511 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 245 = true := by
  have hs : count245 q = (countLit q [124]) + (countLit q [125]) := List.countP_append (p := literal (baseVal q)) (l₁ := [124]) (l₂ := [125])
  have hm := merge_right (literal (valuation q) (125)) (literal (valuation q) (245)) (countLit q [124]) (countLit q [125]) (count245 q) 1 (meaning125 q) (meaning245 q) hs
  change valuation q 125 = false ∨ valuation q 245 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 245 = false ∨ valuation q 247 = true := by
  have hs : count247 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_right (literal (valuation q) (245)) (literal (valuation q) (247)) (countLit q [123]) (countLit q [124, 125]) (count247 q) 1 (meaning245 q) (meaning247 q) hs
  change valuation q 245 = false ∨ valuation q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 247 = true := by
  have hs : count247 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_left (literal (valuation q) (123)) (literal (valuation q) (247)) (countLit q [123]) (countLit q [124, 125]) (count247 q) 1 (meaning123 q) (meaning247 q) hs
  change valuation q 123 = false ∨ valuation q 247 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 245 = false ∨ valuation q 248 = true := by
  have hs : count247 q = (countLit q [123]) + (countLit q [124, 125]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123]) (l₂ := [124, 125])
  have hm := merge_two (literal (valuation q) (123)) (literal (valuation q) (245)) (literal (valuation q) (248)) (countLit q [123]) (countLit q [124, 125]) (count247 q) 1 1 (meaning123 q) (meaning245 q) (meaning248 q) hs
  change valuation q 123 = false ∨ valuation q 245 = false ∨ valuation q 248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 249 = true := by
  have hs : count249 q = (countLit q [126]) + (countLit q [127]) := List.countP_append (p := literal (baseVal q)) (l₁ := [126]) (l₂ := [127])
  have hm := merge_right (literal (valuation q) (127)) (literal (valuation q) (249)) (countLit q [126]) (countLit q [127]) (count249 q) 1 (meaning127 q) (meaning249 q) hs
  change valuation q 127 = false ∨ valuation q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 251 = true := by
  have hs : count251 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal (baseVal q)) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuation q) (129)) (literal (valuation q) (251)) (countLit q [128]) (countLit q [129]) (count251 q) 1 (meaning129 q) (meaning251 q) hs
  change valuation q 129 = false ∨ valuation q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := by
  have hs : count253 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal (baseVal q)) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuation q) (251)) (literal (valuation q) (253)) (countLit q [126, 127]) (countLit q [128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuation q 251 = false ∨ valuation q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 253 = true := by
  have hs : count253 q = (countLit q [126, 127]) + (countLit q [128, 129]) := List.countP_append (p := literal (baseVal q)) (l₁ := [126, 127]) (l₂ := [128, 129])
  have hm := merge_left (literal (valuation q) (249)) (literal (valuation q) (253)) (countLit q [126, 127]) (countLit q [128, 129]) (count253 q) 1 (meaning249 q) (meaning253 q) hs
  change valuation q 249 = false ∨ valuation q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 255 = true := by
  have hs : count255 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_right (literal (valuation q) (253)) (literal (valuation q) (255)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count255 q) 1 (meaning253 q) (meaning255 q) hs
  change valuation q 253 = false ∨ valuation q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 255 = true := by
  have hs : count255 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuation q) (247)) (literal (valuation q) (255)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count255 q) 1 (meaning247 q) (meaning255 q) hs
  change valuation q 247 = false ∨ valuation q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 256 = true := by
  have hs : count255 q = (countLit q [123, 124, 125]) + (countLit q [126, 127, 128, 129]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125]) (l₂ := [126, 127, 128, 129])
  have hm := merge_left (literal (valuation q) (248)) (literal (valuation q) (256)) (countLit q [123, 124, 125]) (countLit q [126, 127, 128, 129]) (count255 q) 2 (meaning248 q) (meaning256 q) hs
  change valuation q 248 = false ∨ valuation q 256 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 257 = true := by
  have hs : count257 q = (countLit q [130]) + (countLit q [131]) := List.countP_append (p := literal (baseVal q)) (l₁ := [130]) (l₂ := [131])
  have hm := merge_right (literal (valuation q) (131)) (literal (valuation q) (257)) (countLit q [130]) (countLit q [131]) (count257 q) 1 (meaning131 q) (meaning257 q) hs
  change valuation q 131 = false ∨ valuation q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 259 = true := by
  have hs : count259 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal (baseVal q)) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuation q) (133)) (literal (valuation q) (259)) (countLit q [132]) (countLit q [133]) (count259 q) 1 (meaning133 q) (meaning259 q) hs
  change valuation q 133 = false ∨ valuation q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 261 = true := by
  have hs : count261 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal (baseVal q)) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_right (literal (valuation q) (259)) (literal (valuation q) (261)) (countLit q [130, 131]) (countLit q [132, 133]) (count261 q) 1 (meaning259 q) (meaning261 q) hs
  change valuation q 259 = false ∨ valuation q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block22 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.First112
