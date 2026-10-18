import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 154 = true ∨ valuation q 45 = true ∨ valuation q 46 = true := by
  rw [value43, value45, value46, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (257 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(259 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (257 : Vertex) (265 : Vertex) [(259 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value2, value44, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (2 : Vertex) (259 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 2 = false ∨ valuation q 54 = false ∨ valuation q 62 = false := by
  rw [value2, value44, value54, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (2 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 2 = false ∨ valuation q 62 = false ∨ valuation q 80 = false := by
  rw [value2, value44, value62, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (2 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 51 = false := by
  rw [value44, value45, value47, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (262 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 54 = false := by
  rw [value44, value45, value47, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (262 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 62 = false := by
  rw [value44, value45, value47, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (262 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 80 = false := by
  rw [value44, value45, value47, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (262 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value44, value45, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 51 = false ∨ valuation q 80 = false := by
  rw [value44, value45, value51, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 80 = false := by
  rw [value44, value45, value54, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value44, value47, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 62 = false := by
  rw [value44, value47, value51, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 51 = false ∨ valuation q 80 = false := by
  rw [value44, value47, value51, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (266 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 62 = false := by
  rw [value44, value47, value54, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 54 = false ∨ valuation q 80 = false := by
  rw [value44, value47, value54, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 62 = false ∨ valuation q 80 = false := by
  rw [value44, value47, value62, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (262 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 62 = false := by
  rw [value44, value51, value54, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (274 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 80 = false := by
  rw [value44, value51, value54, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (274 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 80 = false := by
  rw [value44, value51, value62, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (266 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 62 = false ∨ valuation q 80 = false := by
  rw [value44, value54, value62, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (258 : Vertex) (274 : Vertex) (322 : Vertex) (386 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value43, value44, value45, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ∈ [(257 : Vertex), (258 : Vertex), (263 : Vertex), (267 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (259 : Vertex) [(257 : Vertex), (258 : Vertex), (263 : Vertex), (267 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 156 = true ∨ valuation q 44 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value44, value45, value48, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (257 : Vertex) → w ∈ [(258 : Vertex), (263 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (257 : Vertex) [(258 : Vertex), (263 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 156 = true ∨ valuation q 43 = true ∨ valuation q 48 = true ∨ valuation q 52 = true := by
  rw [value43, value45, value48, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(257 : Vertex), (263 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(257 : Vertex), (263 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 156 = true ∨ valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 52 = true := by
  rw [value43, value44, value45, value52, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (263 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (263 : Vertex) [(257 : Vertex), (258 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 156 = true ∨ valuation q 43 = true ∨ valuation q 44 = true ∨ valuation q 48 = true := by
  rw [value43, value44, value45, value48, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(257 : Vertex), (258 : Vertex), (263 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (267 : Vertex) [(257 : Vertex), (258 : Vertex), (263 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 48 = false ∨ valuation q 82 = false := by
  rw [value43, value46, value48, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (263 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 43 = false ∨ valuation q 64 = false ∨ valuation q 82 = false := by
  rw [value43, value46, value64, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (261 : Vertex) (257 : Vertex) (325 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 157 = true ∨ valuation q 43 = true ∨ valuation q 48 = true ∨ valuation q 64 = true := by
  rw [value43, value46, value48, value64, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (261 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(257 : Vertex), (263 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (261 : Vertex) (389 : Vertex) [(257 : Vertex), (263 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 3 = true ∨ valuation q 44 = true ∨ valuation q 48 = true ∨ valuation q 56 = true ∨ valuation q 65 = true ∨ valuation q 83 = true := by
  rw [value3, value44, value47, value48, value56, value65, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (262 : Vertex) w → w ∈ region → w ∈ [(6 : Vertex), (258 : Vertex), (263 : Vertex), (278 : Vertex), (326 : Vertex), (390 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (262 : Vertex) [(6 : Vertex), (258 : Vertex), (263 : Vertex), (278 : Vertex), (326 : Vertex), (390 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 3 = false ∨ valuation q 48 = false ∨ valuation q 56 = false := by
  rw [value3, value47, value48, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (263 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 3 = false ∨ valuation q 56 = false ∨ valuation q 65 = false := by
  rw [value3, value47, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (262 : Vertex) (6 : Vertex) (278 : Vertex) (326 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E161.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112161
