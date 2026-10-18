import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 183 = true ∨ valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 99 = true := by
  rw [value62, value63, value64, value99, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (320 : Vertex) w → w ∈ region → w ≠ (328 : Vertex) → w ∈ [(321 : Vertex), (324 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (320 : Vertex) (328 : Vertex) [(321 : Vertex), (324 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 63 = true := by
  rw [value63, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (321 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 62 = true ∨ valuation q 100 = true := by
  rw [value62, value63, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ∈ [(320 : Vertex), (449 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (321 : Vertex) [(320 : Vertex), (449 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 100 = true := by
  rw [value63, value100, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(449 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (320 : Vertex) [(449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 184 = true ∨ valuation q 62 = true := by
  rw [value62, value63, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (321 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(320 : Vertex)] := by decide
  have hg := other_cover q (321 : Vertex) (449 : Vertex) [(320 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 8 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value8, value62, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (68 : Vertex) (320 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 8 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value8, value64, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (68 : Vertex) (326 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 68 = false := by
  rw [value62, value64, value65, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (324 : Vertex) (320 : Vertex) (326 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 185 = true ∨ valuation q 62 = true ∨ valuation q 65 = true ∨ valuation q 68 = true := by
  rw [value62, value64, value65, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (324 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(320 : Vertex), (326 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (324 : Vertex) (68 : Vertex) [(320 : Vertex), (326 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 72 = false := by
  rw [value64, value65, value69, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (326 : Vertex) (324 : Vertex) (334 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 186 = true ∨ valuation q 64 = true ∨ valuation q 69 = true := by
  rw [value64, value65, value69, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (326 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(324 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (326 : Vertex) (342 : Vertex) [(324 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 66 = true := by
  rw [value66, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (328 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 74 = true ∨ valuation q 105 = true := by
  rw [value62, value66, value68, value74, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ∈ [(320 : Vertex), (332 : Vertex), (344 : Vertex), (456 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (328 : Vertex) [(320 : Vertex), (332 : Vertex), (344 : Vertex), (456 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 68 = false ∨ valuation q 74 = false := by
  rw [value62, value66, value68, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (332 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 68 = false ∨ valuation q 105 = false := by
  rw [value62, value66, value68, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (328 : Vertex) (320 : Vertex) (332 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 187 = true ∨ valuation q 68 = true ∨ valuation q 74 = true ∨ valuation q 105 = true := by
  rw [value66, value68, value74, value105, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(332 : Vertex), (344 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (320 : Vertex) [(332 : Vertex), (344 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 187 = true ∨ valuation q 62 = true ∨ valuation q 74 = true ∨ valuation q 105 = true := by
  rw [value62, value66, value74, value105, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(320 : Vertex), (344 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (332 : Vertex) [(320 : Vertex), (344 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 187 = true ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 105 = true := by
  rw [value62, value66, value68, value105, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(320 : Vertex), (332 : Vertex), (456 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (344 : Vertex) [(320 : Vertex), (332 : Vertex), (456 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 187 = true ∨ valuation q 62 = true ∨ valuation q 68 = true ∨ valuation q 74 = true := by
  rw [value62, value66, value68, value74, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (328 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(320 : Vertex), (332 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (328 : Vertex) (456 : Vertex) [(320 : Vertex), (332 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 67 = true := by
  rw [value67, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (331 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 12 = true ∨ valuation q 77 = true ∨ valuation q 106 = true := by
  rw [value12, value67, value77, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ∈ [(75 : Vertex), (347 : Vertex), (459 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (331 : Vertex) [(75 : Vertex), (347 : Vertex), (459 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 12 = false ∨ valuation q 77 = false ∨ valuation q 106 = false := by
  rw [value12, value67, value77, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (331 : Vertex) (75 : Vertex) (347 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 12 = false ∨ valuation q 77 = false := by
  rw [value12, value77, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (331 : Vertex) (75 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide)

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 77 = false ∨ valuation q 106 = false := by
  rw [value77, value106, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (331 : Vertex) (347 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 77 = true ∨ valuation q 106 = true := by
  rw [value67, value77, value106, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(347 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (75 : Vertex) [(347 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 12 = true ∨ valuation q 106 = true := by
  rw [value12, value67, value106, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (347 : Vertex) → w ∈ [(75 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (347 : Vertex) [(75 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 188 = true ∨ valuation q 12 = true ∨ valuation q 77 = true := by
  rw [value12, value67, value77, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (459 : Vertex) → w ∈ [(75 : Vertex), (347 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (459 : Vertex) [(75 : Vertex), (347 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value64, value66, value68, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (324 : Vertex) (328 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 107 = false := by
  rw [value64, value66, value68, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (324 : Vertex) (328 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 64 = false ∨ valuation q 69 = false ∨ valuation q 107 = false := by
  rw [value64, value68, value69, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (324 : Vertex) (334 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 66 = false ∨ valuation q 69 = false ∨ valuation q 107 = false := by
  rw [value66, value68, value69, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (328 : Vertex) (334 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 189 = true ∨ valuation q 66 = true ∨ valuation q 69 = true ∨ valuation q 107 = true := by
  rw [value66, value68, value69, value107, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (324 : Vertex) → w ∈ [(328 : Vertex), (334 : Vertex), (460 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (324 : Vertex) [(328 : Vertex), (334 : Vertex), (460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E019.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112019
