import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 184 = true ∨ valuation q 72 = true ∨ valuation q 78 = true := by
  rw [value72, value74, value78, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (326 : Vertex) → w ∈ [(338 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (326 : Vertex) [(338 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 184 = true ∨ valuation q 65 = true ∨ valuation q 78 = true := by
  rw [value65, value74, value78, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (338 : Vertex) → w ∈ [(326 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (338 : Vertex) [(326 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 184 = true ∨ valuation q 65 = true ∨ valuation q 72 = true := by
  rw [value65, value72, value74, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (342 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(326 : Vertex), (338 : Vertex)] := by decide
  have hg := other_cover q (342 : Vertex) (350 : Vertex) [(326 : Vertex), (338 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 58 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value58, value72, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (346 : Vertex) (282 : Vertex) (338 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 185 = true ∨ valuation q 72 = true ∨ valuation q 78 = true := by
  rw [value72, value75, value78, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (346 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(338 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (346 : Vertex) (282 : Vertex) [(338 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 76 = true := by
  rw [value76, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (348 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = true ∨ valuation q 78 = true := by
  rw [value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ∈ [(349 : Vertex), (350 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (348 : Vertex) [(349 : Vertex), (350 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value77, value78, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (348 : Vertex) (349 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 186 = true ∨ valuation q 78 = true := by
  rw [value76, value78, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (349 : Vertex) → w ∈ [(350 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (349 : Vertex) [(350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 186 = true ∨ valuation q 77 = true := by
  rw [value76, value77, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (348 : Vertex) w → w ∈ region → w ≠ (350 : Vertex) → w ∈ [(349 : Vertex)] := by decide
  have hg := other_cover q (348 : Vertex) (350 : Vertex) [(349 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 60 = false ∨ valuation q 69 = false ∨ valuation q 76 = false := by
  rw [value60, value69, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (349 : Vertex) (285 : Vertex) (333 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 187 = true ∨ valuation q 60 = true ∨ valuation q 76 = true := by
  rw [value60, value76, value77, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(285 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (333 : Vertex) [(285 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 187 = true ∨ valuation q 60 = true ∨ valuation q 69 = true := by
  rw [value60, value69, value77, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (349 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(285 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (349 : Vertex) (348 : Vertex) [(285 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false := by
  rw [value74, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (350 : Vertex) (342 : Vertex) (346 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 188 = true ∨ valuation q 75 = true ∨ valuation q 76 = true := by
  rw [value75, value76, value78, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (350 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(346 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (350 : Vertex) (342 : Vertex) [(346 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 190 = true ∨ valuation q 79 = true ∨ valuation q 82 = true := by
  rw [value79, value80, value82, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (418 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(416 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (418 : Vertex) (426 : Vertex) [(416 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 86 = false := by
  rw [value79, value81, value82, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 88 = false := by
  rw [value79, value81, value82, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (422 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value79, value81, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value81, value82, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value80, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (418 : Vertex) (420 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value16, value82, value83, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (167 : Vertex) (422 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 103 = true := by
  rw [value84, value103, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(489 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (441 : Vertex) [(489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 91 = true := by
  rw [value84, value91, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(441 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (489 : Vertex) [(441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 87 = true ∨ valuation q 92 = true := by
  rw [value85, value87, value92, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(430 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (418 : Vertex) [(430 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 80 = true ∨ valuation q 92 = true := by
  rw [value80, value85, value92, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(418 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (430 : Vertex) [(418 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 80 = true ∨ valuation q 87 = true := by
  rw [value80, value85, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(418 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (442 : Vertex) [(418 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 81 = true ∨ valuation q 87 = true := by
  rw [value81, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ∈ [(420 : Vertex), (430 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (428 : Vertex) [(420 : Vertex), (430 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 196 = true ∨ valuation q 87 = true := by
  rw [value86, value87, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 196 = true ∨ valuation q 81 = true := by
  rw [value81, value86, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value82, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = true ∨ valuation q 89 = true := by
  rw [value81, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ∈ [(420 : Vertex), (437 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (436 : Vertex) [(420 : Vertex), (437 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E107.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112107
