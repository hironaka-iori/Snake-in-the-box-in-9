import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 9 = true ∨ valuation q 66 = true := by
  rw [value9, value66, value67, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(99 : Vertex), (354 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(99 : Vertex), (354 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 10 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value10, value68, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (357 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 10 = false ∨ valuation q 72 = false ∨ valuation q 74 = false := by
  rw [value10, value68, value72, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (356 : Vertex) (100 : Vertex) (364 : Vertex) (372 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 190 = true ∨ valuation q 75 = true := by
  rw [value69, value75, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (356 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 190 = true ∨ valuation q 68 = true := by
  rw [value68, value69, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (373 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 66 = false ∨ valuation q 71 = false ∨ valuation q 73 = false := by
  rw [value66, value70, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (354 : Vertex) (363 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 191 = true ∨ valuation q 71 = true ∨ valuation q 73 = true := by
  rw [value70, value71, value73, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (354 : Vertex) → w ∈ [(363 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (354 : Vertex) [(363 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 54 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value54, value67, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 54 = false ∨ valuation q 67 = false ∨ valuation q 79 = false := by
  rw [value54, value67, value71, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 54 = false ∨ valuation q 67 = false ∨ valuation q 110 = false := by
  rw [value54, value67, value71, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (355 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 54 = false ∨ valuation q 70 = false ∨ valuation q 110 = false := by
  rw [value54, value70, value71, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (362 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 54 = false ∨ valuation q 79 = false ∨ valuation q 110 = false := by
  rw [value54, value71, value79, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (299 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 79 = false := by
  rw [value67, value70, value71, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 110 = false := by
  rw [value67, value70, value71, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (362 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 67 = false ∨ valuation q 79 = false ∨ valuation q 110 = false := by
  rw [value67, value71, value79, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 70 = false ∨ valuation q 79 = false ∨ valuation q 110 = false := by
  rw [value70, value71, value79, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (362 : Vertex) (379 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 193 = true ∨ valuation q 73 = true := by
  rw [value72, value73, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(366 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (356 : Vertex) [(366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 193 = true ∨ valuation q 68 = true := by
  rw [value68, value72, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (366 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 194 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(364 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (362 : Vertex) [(364 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 194 = true ∨ valuation q 70 = true := by
  rw [value70, value73, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (364 : Vertex) → w ∈ [(362 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (364 : Vertex) [(362 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 61 = false ∨ valuation q 68 = false ∨ valuation q 75 = false := by
  rw [value61, value68, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (308 : Vertex) (356 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 68 = false ∨ valuation q 75 = false ∨ valuation q 116 = false := by
  rw [value68, value74, value75, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (356 : Vertex) (373 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 69 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value69, value74, value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (373 : Vertex) (357 : Vertex) (372 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 196 = true ∨ valuation q 74 = true ∨ valuation q 76 = true := by
  rw [value74, value75, value76, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (357 : Vertex) → w ∈ [(372 : Vertex), (375 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (357 : Vertex) [(372 : Vertex), (375 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 196 = true ∨ valuation q 69 = true ∨ valuation q 74 = true := by
  rw [value69, value74, value75, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (375 : Vertex) → w ∈ [(357 : Vertex), (372 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (375 : Vertex) [(357 : Vertex), (372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 80 = true := by
  rw [value76, value80, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (373 : Vertex) [(383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 197 = true ∨ valuation q 75 = true := by
  rw [value75, value76, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (375 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(373 : Vertex)] := by decide
  have hg := other_cover q (375 : Vertex) (383 : Vertex) [(373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 198 = true := by
  rw [value77, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (376 : Vertex) (377 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 77 = true ∨ valuation q 79 = true := by
  rw [value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ∈ [(376 : Vertex), (379 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (377 : Vertex) [(376 : Vertex), (379 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 199 = true ∨ valuation q 77 = true := by
  rw [value77, value78, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (377 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (377 : Vertex) (379 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 80 = false := by
  rw [value71, value78, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (363 : Vertex) (377 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 200 = true ∨ valuation q 71 = true ∨ valuation q 80 = true := by
  rw [value71, value79, value80, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(363 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (377 : Vertex) [(363 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block8 (q : Snake 81) (h : Conditions q) : B112E026.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112026
