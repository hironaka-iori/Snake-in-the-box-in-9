import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 35 = false := by
  rw [value13, value14, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (54 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 47 = false := by
  rw [value13, value14, value25, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (54 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 71 = false := by
  rw [value13, value14, value25, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (54 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value13, value14, value35, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (102 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 35 = false ∨ valuation q 71 = false := by
  rw [value13, value14, value35, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (102 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value13, value14, value47, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (39 : Vertex) (166 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 35 = false := by
  rw [value13, value19, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (46 : Vertex) (54 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 47 = false := by
  rw [value13, value19, value25, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (46 : Vertex) (54 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 71 = false := by
  rw [value13, value19, value25, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (46 : Vertex) (54 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value13, value19, value35, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (46 : Vertex) (102 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 35 = false ∨ valuation q 71 = false := by
  rw [value13, value19, value35, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (46 : Vertex) (102 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 19 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value13, value19, value47, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (46 : Vertex) (166 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 35 = false ∨ valuation q 47 = false := by
  rw [value13, value25, value35, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (54 : Vertex) (102 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 35 = false ∨ valuation q 71 = false := by
  rw [value13, value25, value35, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (54 : Vertex) (102 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 25 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value13, value25, value47, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (54 : Vertex) (166 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 35 = false ∨ valuation q 47 = false ∨ valuation q 71 = false := by
  rw [value13, value35, value47, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (38 : Vertex) (102 : Vertex) (166 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 140 = true ∨ valuation q 13 = true ∨ valuation q 26 = true ∨ valuation q 72 = true := by
  rw [value13, value14, value26, value72, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (37 : Vertex) → w ∈ [(38 : Vertex), (55 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (37 : Vertex) [(38 : Vertex), (55 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 140 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 72 = true := by
  rw [value12, value13, value14, value72, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (55 : Vertex) → w ∈ [(37 : Vertex), (38 : Vertex), (295 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (55 : Vertex) [(37 : Vertex), (38 : Vertex), (295 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 140 = true ∨ valuation q 12 = true ∨ valuation q 13 = true ∨ valuation q 26 = true := by
  rw [value12, value13, value14, value26, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (39 : Vertex) w → w ∈ region → w ≠ (295 : Vertex) → w ∈ [(37 : Vertex), (38 : Vertex), (55 : Vertex)] := by decide
  have hg := other_cover q (39 : Vertex) (295 : Vertex) [(37 : Vertex), (38 : Vertex), (55 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value8, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (32 : Vertex) (41 : Vertex) (42 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value8, value15, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (32 : Vertex) (41 : Vertex) (44 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 17 = false ∨ valuation q 73 = false := by
  rw [value8, value15, value17, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (32 : Vertex) (42 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 8 = false ∨ valuation q 18 = false ∨ valuation q 73 = false := by
  rw [value8, value15, value18, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (32 : Vertex) (44 : Vertex) (296 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 48 = false := by
  rw [value15, value16, value17, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (40 : Vertex) (41 : Vertex) (42 : Vertex) (168 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 27 = false := by
  rw [value9, value15, value16, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (40 : Vertex) (57 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 36 = false := by
  rw [value9, value15, value16, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (40 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 36 = false := by
  rw [value9, value16, value27, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (57 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 9 = false ∨ valuation q 27 = false ∨ valuation q 74 = false := by
  rw [value9, value16, value27, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (57 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 9 = false ∨ valuation q 36 = false ∨ valuation q 74 = false := by
  rw [value9, value16, value36, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (33 : Vertex) (105 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 36 = false := by
  rw [value15, value16, value27, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (57 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 27 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value27, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (57 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 15 = false ∨ valuation q 36 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value36, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (41 : Vertex) (40 : Vertex) (105 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E121.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112121
