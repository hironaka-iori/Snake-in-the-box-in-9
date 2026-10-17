import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 152 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(302 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (268 : Vertex) [(302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 152 = true ∨ valuation q 14 = true := by
  rw [value14, value30, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (300 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(268 : Vertex)] := by decide
  have hg := other_cover q (300 : Vertex) (302 : Vertex) [(268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 40 = false ∨ valuation q 90 = false := by
  rw [value30, value31, value40, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (302 : Vertex) (300 : Vertex) (318 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 40 = true ∨ valuation q 90 = true := by
  rw [value31, value40, value90, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(318 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (300 : Vertex) [(318 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 30 = true ∨ valuation q 90 = true := by
  rw [value30, value31, value90, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(300 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (318 : Vertex) [(300 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 153 = true ∨ valuation q 30 = true ∨ valuation q 40 = true := by
  rw [value30, value31, value40, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(300 : Vertex), (318 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (430 : Vertex) [(300 : Vertex), (318 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 33 = false := by
  rw [value16, value24, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (272 : Vertex) (288 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 35 = false := by
  rw [value16, value24, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (272 : Vertex) (288 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 37 = false := by
  rw [value16, value24, value32, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (272 : Vertex) (288 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 24 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value24, value32, value33, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (305 : Vertex) (308 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 24 = false ∨ valuation q 33 = false ∨ valuation q 37 = false := by
  rw [value24, value32, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (305 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 24 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value24, value32, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (308 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 24 = false ∨ valuation q 35 = false ∨ valuation q 91 = false := by
  rw [value24, value32, value35, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (288 : Vertex) (308 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (305 : Vertex) (308 : Vertex) (312 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 91 = false := by
  rw [value32, value33, value35, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (304 : Vertex) (305 : Vertex) (308 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 33 = true := by
  rw [value33, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (305 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 92 = false := by
  rw [value32, value33, value34, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (304 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 32 = false ∨ valuation q 34 = false := by
  rw [value32, value34, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (305 : Vertex) (304 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 155 = true ∨ valuation q 32 = true ∨ valuation q 92 = true := by
  rw [value32, value33, value92, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(304 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(304 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 155 = true ∨ valuation q 32 = true ∨ valuation q 34 = true := by
  rw [value32, value33, value34, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (433 : Vertex) → w ∈ [(304 : Vertex), (307 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (433 : Vertex) [(304 : Vertex), (307 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 33 = true ∨ valuation q 93 = true := by
  rw [value33, value34, value93, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(305 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (275 : Vertex) [(305 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 17 = true ∨ valuation q 93 = true := by
  rw [value17, value34, value93, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(275 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(275 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 156 = true ∨ valuation q 17 = true ∨ valuation q 33 = true := by
  rw [value17, value33, value34, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(275 : Vertex), (305 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (435 : Vertex) [(275 : Vertex), (305 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 36 = false := by
  rw [value18, value32, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (276 : Vertex) (304 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 18 = false ∨ valuation q 32 = false ∨ valuation q 94 = false := by
  rw [value18, value32, value35, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (276 : Vertex) (304 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 18 = false ∨ valuation q 36 = false ∨ valuation q 94 = false := by
  rw [value18, value35, value36, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (276 : Vertex) (310 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 94 = false := by
  rw [value32, value35, value36, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (308 : Vertex) (304 : Vertex) (310 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 32 = true ∨ valuation q 36 = true ∨ valuation q 94 = true := by
  rw [value32, value35, value36, value94, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(304 : Vertex), (310 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (276 : Vertex) [(304 : Vertex), (310 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 18 = true ∨ valuation q 32 = true ∨ valuation q 94 = true := by
  rw [value18, value32, value35, value94, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(276 : Vertex), (304 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (310 : Vertex) [(276 : Vertex), (304 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 157 = true ∨ valuation q 18 = true ∨ valuation q 32 = true ∨ valuation q 36 = true := by
  rw [value18, value32, value35, value36, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(276 : Vertex), (304 : Vertex), (310 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (436 : Vertex) [(276 : Vertex), (304 : Vertex), (310 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 158 = true ∨ valuation q 40 = true ∨ valuation q 96 = true := by
  rw [value36, value40, value96, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(318 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (308 : Vertex) [(318 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 158 = true ∨ valuation q 35 = true ∨ valuation q 96 = true := by
  rw [value35, value36, value96, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (318 : Vertex) → w ∈ [(308 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (318 : Vertex) [(308 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E254.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112254
