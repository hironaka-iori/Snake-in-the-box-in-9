import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 159 = true ∨ valuation q 56 = true ∨ valuation q 58 = true := by
  rw [value55, value56, value58, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(267 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(267 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 159 = true ∨ valuation q 51 = true ∨ valuation q 58 = true := by
  rw [value51, value55, value58, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(258 : Vertex), (270 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (267 : Vertex) [(258 : Vertex), (270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 159 = true ∨ valuation q 51 = true ∨ valuation q 56 = true := by
  rw [value51, value55, value56, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex), (267 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex), (267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 1 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value1, value52, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 1 = false ∨ valuation q 52 = false ∨ valuation q 65 = false := by
  rw [value1, value52, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 1 = false ∨ valuation q 55 = false ∨ valuation q 65 = false := by
  rw [value1, value55, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (11 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 65 = false := by
  rw [value52, value55, value56, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (267 : Vertex) (259 : Vertex) (266 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 1 = false ∨ valuation q 52 = false := by
  rw [value1, value52, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (267 : Vertex) (11 : Vertex) (259 : Vertex) (by decide) (by decide) (by decide)

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 1 = false ∨ valuation q 55 = false := by
  rw [value1, value55, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (267 : Vertex) (11 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide)

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 160 = true ∨ valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value52, value55, value56, value65, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (11 : Vertex) → w ∈ [(259 : Vertex), (266 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (11 : Vertex) [(259 : Vertex), (266 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 160 = true ∨ valuation q 1 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value1, value55, value56, value65, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(11 : Vertex), (266 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (259 : Vertex) [(11 : Vertex), (266 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 160 = true ∨ valuation q 1 = true ∨ valuation q 52 = true ∨ valuation q 65 = true := by
  rw [value1, value52, value56, value65, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (267 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(11 : Vertex), (259 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (267 : Vertex) (266 : Vertex) [(11 : Vertex), (259 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 58 = true := by
  rw [value57, value58, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (260 : Vertex) [(270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 161 = true ∨ valuation q 53 = true := by
  rw [value53, value57, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 55 = true ∨ valuation q 57 = true := by
  rw [value55, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ∈ [(266 : Vertex), (268 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (270 : Vertex) [(266 : Vertex), (268 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 162 = true ∨ valuation q 57 = true := by
  rw [value57, value58, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(268 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (266 : Vertex) [(268 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 162 = true ∨ valuation q 55 = true := by
  rw [value55, value58, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(266 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = true ∨ valuation q 63 = true ∨ valuation q 76 = true := by
  rw [value59, value60, value63, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ∈ [(276 : Vertex), (280 : Vertex), (400 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (272 : Vertex) [(276 : Vertex), (280 : Vertex), (400 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 63 = false ∨ valuation q 76 = false := by
  rw [value59, value60, value63, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 63 = true ∨ valuation q 76 = true := by
  rw [value59, value63, value76, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(280 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(280 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 60 = true ∨ valuation q 76 = true := by
  rw [value59, value60, value76, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(276 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(276 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 163 = true ∨ valuation q 60 = true ∨ valuation q 63 = true := by
  rw [value59, value60, value63, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(276 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (400 : Vertex) [(276 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 53 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value53, value59, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 59 = true ∨ valuation q 61 = true := by
  rw [value59, value60, value61, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(272 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (260 : Vertex) [(272 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 53 = true ∨ valuation q 61 = true := by
  rw [value53, value60, value61, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(260 : Vertex), (277 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (272 : Vertex) [(260 : Vertex), (277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 164 = true ∨ valuation q 53 = true ∨ valuation q 59 = true := by
  rw [value53, value59, value60, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex), (272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 54 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value54, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 165 = true ∨ valuation q 60 = true ∨ valuation q 62 = true := by
  rw [value60, value61, value62, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(276 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (261 : Vertex) [(276 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 165 = true ∨ valuation q 54 = true ∨ valuation q 62 = true := by
  rw [value54, value61, value62, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(261 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(261 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 165 = true ∨ valuation q 54 = true ∨ valuation q 60 = true := by
  rw [value54, value60, value61, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(261 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (279 : Vertex) [(261 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 166 = true ∨ valuation q 66 = true := by
  rw [value62, value66, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(287 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (277 : Vertex) [(287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 166 = true ∨ valuation q 61 = true := by
  rw [value61, value62, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block5 (q : Snake 81) (h : Conditions q) : B112E174.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112174
