import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 60 = true ∨ valuation q 96 = true := by
  rw [value59, value60, value96, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(284 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(284 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 53 = true ∨ valuation q 96 = true := by
  rw [value53, value59, value96, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(272 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (284 : Vertex) [(272 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 177 = true ∨ valuation q 53 = true ∨ valuation q 60 = true := by
  rw [value53, value59, value60, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(272 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (408 : Vertex) [(272 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value57, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (276 : Vertex) (280 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value58, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (286 : Vertex) (278 : Vertex) (284 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 58 = false ∨ valuation q 62 = false := by
  rw [value58, value62, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (286 : Vertex) (278 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 179 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value58, value60, value61, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (287 : Vertex) [(278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = true := by
  rw [value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ∈ [(286 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (287 : Vertex) [(286 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 62 = true := by
  rw [value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value63, value64, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (320 : Vertex) (321 : Vertex) (322 : Vertex) (328 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value63, value65, value68, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(322 : Vertex), (328 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (321 : Vertex) [(322 : Vertex), (328 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 181 = true ∨ valuation q 64 = true ∨ valuation q 65 = true := by
  rw [value63, value64, value65, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex), (322 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(321 : Vertex), (322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 182 = true ∨ valuation q 63 = true ∨ valuation q 69 = true := by
  rw [value63, value64, value69, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (65 : Vertex) [(320 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 182 = true ∨ valuation q 8 = true ∨ valuation q 69 = true := by
  rw [value8, value64, value69, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(65 : Vertex), (329 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(65 : Vertex), (329 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 182 = true ∨ valuation q 8 = true ∨ valuation q 63 = true := by
  rw [value8, value63, value64, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (329 : Vertex) → w ∈ [(65 : Vertex), (320 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (329 : Vertex) [(65 : Vertex), (320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 50 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value50, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 50 = false ∨ valuation q 66 = false ∨ valuation q 73 = false := by
  rw [value50, value65, value66, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 50 = false ∨ valuation q 66 = false ∨ valuation q 101 = false := by
  rw [value50, value65, value66, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (326 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 50 = false ∨ valuation q 73 = false ∨ valuation q 101 = false := by
  rw [value50, value65, value73, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (258 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 70 = false := by
  rw [value63, value65, value66, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 63 = false ∨ valuation q 66 = false ∨ valuation q 73 = false := by
  rw [value63, value65, value66, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (320 : Vertex) (326 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 101 = false := by
  rw [value65, value66, value70, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (326 : Vertex) (330 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 73 = false ∨ valuation q 101 = false := by
  rw [value65, value66, value73, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (322 : Vertex) (326 : Vertex) (338 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 72 = false := by
  rw [value65, value66, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (322 : Vertex) (327 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 65 = true ∨ valuation q 72 = true := by
  rw [value65, value66, value72, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(322 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (327 : Vertex) [(322 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 184 = true ∨ valuation q 65 = true ∨ valuation q 67 = true := by
  rw [value65, value66, value67, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(322 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (334 : Vertex) [(322 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 75 = true := by
  rw [value67, value75, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(343 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (326 : Vertex) [(343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 185 = true ∨ valuation q 66 = true := by
  rw [value66, value67, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(326 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (343 : Vertex) [(326 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 10 = false ∨ valuation q 63 = false ∨ valuation q 71 = false := by
  rw [value10, value63, value68, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (320 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 10 = false ∨ valuation q 69 = false ∨ valuation q 71 = false := by
  rw [value10, value68, value69, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (72 : Vertex) (329 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 63 = true ∨ valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 71 = true := by
  rw [value63, value68, value69, value70, value71, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(320 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (72 : Vertex) [(320 : Vertex), (329 : Vertex), (330 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 186 = true ∨ valuation q 10 = true ∨ valuation q 63 = true ∨ valuation q 69 = true ∨ valuation q 70 = true := by
  rw [value10, value63, value68, value69, value70, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(72 : Vertex), (320 : Vertex), (329 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (332 : Vertex) [(72 : Vertex), (320 : Vertex), (329 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E007.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112007
