import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 160 = true ∨ valuation q 40 = true := by
  rw [value39, value40, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 160 = true ∨ valuation q 34 = true := by
  rw [value34, value39, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(228 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (230 : Vertex) (234 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 39 = true := by
  rw [value36, value39, value40, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (234 : Vertex) → w ∈ [(230 : Vertex), (236 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (234 : Vertex) [(230 : Vertex), (236 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value40, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(230 : Vertex), (234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(230 : Vertex), (234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 34 = false ∨ valuation q 42 = false ∨ valuation q 116 = false := by
  rw [value34, value41, value42, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (228 : Vertex) (245 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 162 = true ∨ valuation q 34 = true ∨ valuation q 116 = true := by
  rw [value34, value41, value116, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(228 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 43 = false := by
  rw [value35, value41, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 163 = true ∨ valuation q 41 = true ∨ valuation q 43 = true := by
  rw [value41, value42, value43, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (229 : Vertex) → w ∈ [(244 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (229 : Vertex) [(244 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 163 = true ∨ valuation q 35 = true ∨ valuation q 41 = true := by
  rw [value35, value41, value42, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(229 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (247 : Vertex) [(229 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 48 = true := by
  rw [value43, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 164 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 45 = true ∨ valuation q 46 = true := by
  rw [value44, value45, value46, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(249 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(249 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 27 = true ∨ valuation q 46 = true := by
  rw [value27, value44, value46, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(184 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(184 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 165 = true ∨ valuation q 27 = true ∨ valuation q 45 = true := by
  rw [value27, value44, value45, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(184 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (250 : Vertex) [(184 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 47 = true := by
  rw [value45, value47, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 166 = true ∨ valuation q 44 = true := by
  rw [value44, value45, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (251 : Vertex) [(248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value37, value44, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 44 = false ∨ valuation q 118 = false := by
  rw [value37, value44, value46, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 118 = false := by
  rw [value37, value46, value47, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 118 = false := by
  rw [value44, value46, value47, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (248 : Vertex) (251 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 38 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value38, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 38 = false ∨ valuation q 46 = false ∨ valuation q 48 = false := by
  rw [value38, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (250 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 168 = true ∨ valuation q 38 = true ∨ valuation q 45 = true ∨ valuation q 48 = true := by
  rw [value38, value45, value47, value48, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (250 : Vertex) [(235 : Vertex), (249 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 31 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value31, value43, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 57 = false := by
  rw [value49, value50, value53, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (304 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 53 = false ∨ valuation q 81 = false := by
  rw [value49, value50, value53, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 81 = false := by
  rw [value49, value50, value57, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 81 = false := by
  rw [value49, value53, value57, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (288 : Vertex) (296 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 50 = false ∨ valuation q 57 = false := by
  rw [value50, value57, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (by decide) (by decide) (by decide)

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 57 = false ∨ valuation q 81 = false := by
  rw [value57, value81, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (288 : Vertex) (304 : Vertex) (416 : Vertex) (by decide) (by decide) (by decide)

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 170 = true ∨ valuation q 53 = true ∨ valuation q 57 = true ∨ valuation q 81 = true := by
  rw [value49, value53, value57, value81, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (288 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(296 : Vertex), (304 : Vertex), (416 : Vertex)] := by decide
  have hg := other_cover q (288 : Vertex) (289 : Vertex) [(296 : Vertex), (304 : Vertex), (416 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E026.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112026
