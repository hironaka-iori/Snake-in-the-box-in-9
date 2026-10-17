import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value30, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (155 : Vertex) (153 : Vertex) (154 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 31 = true ∨ valuation q 33 = true := by
  rw [value31, value32, value33, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(154 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (153 : Vertex) [(154 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 30 = true ∨ valuation q 33 = true := by
  rw [value30, value32, value33, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(153 : Vertex), (159 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (154 : Vertex) [(153 : Vertex), (159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 150 = true ∨ valuation q 30 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value32, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (155 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(153 : Vertex), (154 : Vertex)] := by decide
  have hg := other_cover q (155 : Vertex) (159 : Vertex) [(153 : Vertex), (154 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 32 = true := by
  rw [value32, value33, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(155 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (151 : Vertex) [(155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 151 = true ∨ valuation q 29 = true := by
  rw [value29, value33, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (159 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(151 : Vertex)] := by decide
  have hg := other_cover q (159 : Vertex) (155 : Vertex) [(151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 15 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value15, value34, value35, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (192 : Vertex) (128 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 152 = true ∨ valuation q 15 = true ∨ valuation q 35 = true := by
  rw [value15, value34, value35, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (192 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(128 : Vertex), (193 : Vertex)] := by decide
  have hg := other_cover q (192 : Vertex) (200 : Vertex) [(128 : Vertex), (193 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 9 = false ∨ valuation q 34 = false ∨ valuation q 40 = false := by
  rw [value9, value34, value35, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 9 = false ∨ valuation q 34 = false ∨ valuation q 43 = false := by
  rw [value9, value34, value35, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (193 : Vertex) (65 : Vertex) (192 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 153 = true ∨ valuation q 9 = true ∨ valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 40 = true := by
  rw [value9, value34, value35, value36, value40, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (193 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(65 : Vertex), (192 : Vertex), (197 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (193 : Vertex) (209 : Vertex) [(65 : Vertex), (192 : Vertex), (197 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value35, value36, value38, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 104 = false := by
  rw [value35, value36, value38, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (199 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 104 = false := by
  rw [value35, value36, value41, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (193 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 104 = false := by
  rw [value36, value38, value41, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 38 = false := by
  rw [value11, value19, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 46 = false := by
  rw [value11, value19, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (134 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 11 = false ∨ valuation q 38 = false ∨ valuation q 46 = false := by
  rw [value11, value37, value38, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (198 : Vertex) (70 : Vertex) (199 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 156 = true ∨ valuation q 20 = true ∨ valuation q 37 = true ∨ valuation q 42 = true := by
  rw [value20, value37, value38, value42, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(135 : Vertex), (198 : Vertex), (207 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (197 : Vertex) [(135 : Vertex), (198 : Vertex), (207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 156 = true ∨ valuation q 20 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value20, value36, value37, value38, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (199 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(135 : Vertex), (197 : Vertex), (198 : Vertex)] := by decide
  have hg := other_cover q (199 : Vertex) (207 : Vertex) [(135 : Vertex), (197 : Vertex), (198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 39 = true := by
  rw [value39, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (200 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 12 = true ∨ valuation q 21 = true ∨ valuation q 34 = true ∨ valuation q 40 = true := by
  rw [value12, value21, value34, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ∈ [(72 : Vertex), (136 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (200 : Vertex) [(72 : Vertex), (136 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 21 = true ∨ valuation q 34 = true ∨ valuation q 40 = true := by
  rw [value21, value34, value39, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(136 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (72 : Vertex) [(136 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 12 = true ∨ valuation q 34 = true ∨ valuation q 40 = true := by
  rw [value12, value34, value39, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(72 : Vertex), (192 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (136 : Vertex) [(72 : Vertex), (192 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 157 = true ∨ valuation q 12 = true ∨ valuation q 21 = true ∨ valuation q 40 = true := by
  rw [value12, value21, value39, value40, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (200 : Vertex) w → w ∈ region → w ≠ (192 : Vertex) → w ∈ [(72 : Vertex), (136 : Vertex), (201 : Vertex)] := by decide
  have hg := other_cover q (200 : Vertex) (192 : Vertex) [(72 : Vertex), (136 : Vertex), (201 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 22 = false ∨ valuation q 35 = false ∨ valuation q 39 = false := by
  rw [value22, value35, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (200 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 22 = false ∨ valuation q 35 = false ∨ valuation q 41 = false := by
  rw [value22, value35, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (193 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 22 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value22, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (137 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 35 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value35, value39, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (193 : Vertex) (200 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 105 = false := by
  rw [value39, value40, value41, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (201 : Vertex) (200 : Vertex) (205 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 49 = false := by
  rw [value36, value40, value41, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (197 : Vertex) (201 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 159 = true ∨ valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 49 = true := by
  rw [value40, value41, value42, value49, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(201 : Vertex), (207 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (197 : Vertex) [(201 : Vertex), (207 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E027.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112027
