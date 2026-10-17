import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 189 = true ∨ valuation q 51 = true ∨ valuation q 60 = true := by
  rw [value51, value60, value61, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (275 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(259 : Vertex), (274 : Vertex)] := by decide
  have hg := other_cover q (275 : Vertex) (279 : Vertex) [(259 : Vertex), (274 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 80 = false ∨ valuation q 102 = false := by
  rw [value61, value62, value80, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (275 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 80 = false ∨ valuation q 102 = false := by
  rw [value62, value67, value80, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (287 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 67 = true ∨ valuation q 80 = true ∨ valuation q 102 = true := by
  rw [value62, value67, value80, value102, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(287 : Vertex), (343 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (275 : Vertex) [(287 : Vertex), (343 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 61 = true ∨ valuation q 80 = true ∨ valuation q 102 = true := by
  rw [value61, value62, value80, value102, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(275 : Vertex), (343 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(275 : Vertex), (343 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 102 = true := by
  rw [value61, value62, value67, value102, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (343 : Vertex) [(275 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 190 = true ∨ valuation q 61 = true ∨ valuation q 67 = true ∨ valuation q 80 = true := by
  rw [value61, value62, value67, value80, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(275 : Vertex), (287 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(275 : Vertex), (287 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 81 = false := by
  rw [value59, value63, value64, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (284 : Vertex) (344 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 191 = true ∨ valuation q 64 = true ∨ valuation q 81 = true := by
  rw [value63, value64, value81, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(284 : Vertex), (344 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(284 : Vertex), (344 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 191 = true ∨ valuation q 59 = true ∨ valuation q 64 = true := by
  rw [value59, value63, value64, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(272 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (344 : Vertex) [(272 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 56 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value56, value63, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (280 : Vertex) (285 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 56 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value56, value63, value64, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (280 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 56 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value56, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (268 : Vertex) (285 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value63, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (284 : Vertex) (280 : Vertex) (285 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 57 = false ∨ valuation q 64 = false ∨ valuation q 106 = false := by
  rw [value57, value64, value65, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (269 : Vertex) (284 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 57 = false ∨ valuation q 67 = false ∨ valuation q 106 = false := by
  rw [value57, value65, value67, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (285 : Vertex) (269 : Vertex) (287 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 106 = true := by
  rw [value64, value65, value67, value106, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(284 : Vertex), (287 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (269 : Vertex) [(284 : Vertex), (287 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 57 = true ∨ valuation q 67 = true ∨ valuation q 106 = true := by
  rw [value57, value65, value67, value106, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(269 : Vertex), (287 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (284 : Vertex) [(269 : Vertex), (287 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 106 = true := by
  rw [value57, value64, value65, value106, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(269 : Vertex), (284 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (287 : Vertex) [(269 : Vertex), (284 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 193 = true ∨ valuation q 57 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value57, value64, value65, value67, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (285 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(269 : Vertex), (284 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (285 : Vertex) (413 : Vertex) [(269 : Vertex), (284 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 58 = false ∨ valuation q 67 = false ∨ valuation q 107 = false := by
  rw [value58, value66, value67, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (286 : Vertex) (270 : Vertex) (287 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 107 = false := by
  rw [value64, value66, value67, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (286 : Vertex) (284 : Vertex) (287 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true ∨ valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 107 = true := by
  rw [value64, value66, value67, value107, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(284 : Vertex), (287 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (270 : Vertex) [(284 : Vertex), (287 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 67 = true ∨ valuation q 107 = true := by
  rw [value58, value66, value67, value107, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(270 : Vertex), (287 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (284 : Vertex) [(270 : Vertex), (287 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 64 = true ∨ valuation q 107 = true := by
  rw [value58, value64, value66, value107, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(270 : Vertex), (284 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (287 : Vertex) [(270 : Vertex), (284 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 194 = true ∨ valuation q 58 = true ∨ valuation q 64 = true ∨ valuation q 67 = true := by
  rw [value58, value64, value66, value67, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (286 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(270 : Vertex), (284 : Vertex), (287 : Vertex)] := by decide
  have hg := other_cover q (286 : Vertex) (414 : Vertex) [(270 : Vertex), (284 : Vertex), (287 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value62, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (285 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 85 = false := by
  rw [value62, value65, value67, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (285 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 108 = false := by
  rw [value62, value65, value67, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (285 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 85 = false := by
  rw [value62, value66, value67, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (286 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 108 = false := by
  rw [value62, value66, value67, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (286 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 62 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value62, value67, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (287 : Vertex) (279 : Vertex) (351 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E050.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112050
