import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 63 = false := by
  rw [value53, value55, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (218 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 103 = false := by
  rw [value53, value55, value56, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (218 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 103 = false := by
  rw [value53, value56, value63, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (203 : Vertex) (251 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 103 = false := by
  rw [value55, value56, value63, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (219 : Vertex) (218 : Vertex) (251 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 162 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true ∨ valuation q 103 = true := by
  rw [value53, value55, value56, value63, value103, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (91 : Vertex) → w ∈ [(203 : Vertex), (218 : Vertex), (251 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (91 : Vertex) [(203 : Vertex), (218 : Vertex), (251 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 162 = true ∨ valuation q 30 = true ∨ valuation q 53 = true ∨ valuation q 63 = true ∨ valuation q 103 = true := by
  rw [value30, value53, value56, value63, value103, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(91 : Vertex), (203 : Vertex), (251 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (218 : Vertex) [(91 : Vertex), (203 : Vertex), (251 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 162 = true ∨ valuation q 30 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 103 = true := by
  rw [value30, value53, value55, value56, value103, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(91 : Vertex), (203 : Vertex), (218 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (251 : Vertex) [(91 : Vertex), (203 : Vertex), (218 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 162 = true ∨ valuation q 30 = true ∨ valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 63 = true := by
  rw [value30, value53, value55, value56, value63, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (219 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(91 : Vertex), (203 : Vertex), (218 : Vertex), (251 : Vertex)] := by decide
  have hg := other_cover q (219 : Vertex) (475 : Vertex) [(91 : Vertex), (203 : Vertex), (218 : Vertex), (251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 34 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value34, value57, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (160 : Vertex) (232 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 163 = true ∨ valuation q 58 = true ∨ valuation q 60 = true := by
  rw [value57, value58, value60, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(232 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (160 : Vertex) [(232 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 60 = true := by
  rw [value34, value57, value60, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(160 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (232 : Vertex) [(160 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 163 = true ∨ valuation q 34 = true ∨ valuation q 58 = true := by
  rw [value34, value57, value58, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (224 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(160 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (224 : Vertex) (240 : Vertex) [(160 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 37 = false ∨ valuation q 52 = false ∨ valuation q 57 = false := by
  rw [value37, value52, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (168 : Vertex) (200 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 164 = true ∨ valuation q 52 = true ∨ valuation q 57 = true := by
  rw [value52, value57, value58, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(200 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (168 : Vertex) [(200 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 164 = true ∨ valuation q 37 = true ∨ valuation q 57 = true := by
  rw [value37, value57, value58, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (200 : Vertex) → w ∈ [(168 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (200 : Vertex) [(168 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 164 = true ∨ valuation q 37 = true ∨ valuation q 52 = true := by
  rw [value37, value52, value58, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(168 : Vertex), (200 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (224 : Vertex) [(168 : Vertex), (200 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 165 = true ∨ valuation q 41 = true := by
  rw [value41, value59, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(174 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (254 : Vertex) [(174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 57 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value57, value60, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (224 : Vertex) (242 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 166 = true ∨ valuation q 61 = true ∨ valuation q 62 = true := by
  rw [value60, value61, value62, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (224 : Vertex) → w ∈ [(242 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (224 : Vertex) [(242 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 166 = true ∨ valuation q 57 = true ∨ valuation q 61 = true := by
  rw [value57, value60, value61, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(224 : Vertex), (242 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (244 : Vertex) [(224 : Vertex), (242 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 60 = true := by
  rw [value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ∈ [(240 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (242 : Vertex) [(240 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 167 = true := by
  rw [value61, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (242 : Vertex) (240 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 43 = false ∨ valuation q 60 = false ∨ valuation q 64 = false := by
  rw [value43, value60, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (244 : Vertex) (180 : Vertex) (240 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 168 = true ∨ valuation q 43 = true ∨ valuation q 64 = true := by
  rw [value43, value62, value64, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(180 : Vertex), (252 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (240 : Vertex) [(180 : Vertex), (252 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 168 = true ∨ valuation q 43 = true ∨ valuation q 60 = true := by
  rw [value43, value60, value62, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(180 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (252 : Vertex) [(180 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 66 = true := by
  rw [value50, value63, value66, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (219 : Vertex) → w ∈ [(187 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (219 : Vertex) [(187 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 169 = true ∨ valuation q 50 = true ∨ valuation q 56 = true := by
  rw [value50, value56, value63, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(187 : Vertex), (219 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(187 : Vertex), (219 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 170 = true ∨ valuation q 65 = true := by
  rw [value64, value65, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(254 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (244 : Vertex) [(254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 170 = true ∨ valuation q 62 = true := by
  rw [value62, value64, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (252 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(244 : Vertex)] := by decide
  have hg := other_cover q (252 : Vertex) (254 : Vertex) [(244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 59 = false ∨ valuation q 64 = false ∨ valuation q 66 = false := by
  rw [value59, value64, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (238 : Vertex) (252 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 171 = true ∨ valuation q 64 = true ∨ valuation q 66 = true := by
  rw [value64, value65, value66, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(252 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (238 : Vertex) [(252 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 171 = true ∨ valuation q 59 = true ∨ valuation q 66 = true := by
  rw [value59, value65, value66, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (252 : Vertex) → w ∈ [(238 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (252 : Vertex) [(238 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E091.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112091
