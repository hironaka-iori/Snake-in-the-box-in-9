import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 165 = true ∨ valuation q 14 = true ∨ valuation q 34 = true ∨ valuation q 47 = true := by
  rw [value14, value34, value47, value51, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (203 : Vertex) w → w ∈ region → w ≠ (202 : Vertex) → w ∈ [(75 : Vertex), (139 : Vertex), (195 : Vertex)] := by decide
  have hg := other_cover q (203 : Vertex) (202 : Vertex) [(75 : Vertex), (139 : Vertex), (195 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 15 = false ∨ valuation q 35 = false ∨ valuation q 48 = false := by
  rw [value15, value35, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 15 = false ∨ valuation q 35 = false ∨ valuation q 53 = false := by
  rw [value15, value35, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (140 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 53 = false := by
  rw [value15, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (76 : Vertex) (196 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 35 = false ∨ valuation q 48 = false ∨ valuation q 53 = false := by
  rw [value35, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (204 : Vertex) (140 : Vertex) (196 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 166 = true ∨ valuation q 15 = true ∨ valuation q 48 = true ∨ valuation q 53 = true := by
  rw [value15, value48, value52, value53, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(76 : Vertex), (196 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (140 : Vertex) [(76 : Vertex), (196 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 166 = true ∨ valuation q 15 = true ∨ valuation q 35 = true ∨ valuation q 53 = true := by
  rw [value15, value35, value52, value53, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (204 : Vertex) w → w ∈ region → w ≠ (196 : Vertex) → w ∈ [(76 : Vertex), (140 : Vertex), (205 : Vertex)] := by decide
  have hg := other_cover q (204 : Vertex) (196 : Vertex) [(76 : Vertex), (140 : Vertex), (205 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 36 = false ∨ valuation q 52 = false := by
  rw [value16, value36, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (77 : Vertex) (141 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 36 = false ∨ valuation q 61 = false := by
  rw [value16, value36, value53, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (77 : Vertex) (141 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 16 = false ∨ valuation q 52 = false ∨ valuation q 61 = false := by
  rw [value16, value52, value53, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (77 : Vertex) (204 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 36 = false ∨ valuation q 52 = false ∨ valuation q 61 = false := by
  rw [value36, value52, value53, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (205 : Vertex) (141 : Vertex) (204 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 167 = true ∨ valuation q 36 = true ∨ valuation q 52 = true ∨ valuation q 61 = true := by
  rw [value36, value52, value53, value61, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (77 : Vertex) → w ∈ [(141 : Vertex), (204 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (77 : Vertex) [(141 : Vertex), (204 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 167 = true ∨ valuation q 16 = true ∨ valuation q 52 = true ∨ valuation q 61 = true := by
  rw [value16, value52, value53, value61, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(77 : Vertex), (204 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (141 : Vertex) [(77 : Vertex), (204 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 167 = true ∨ valuation q 16 = true ∨ valuation q 36 = true ∨ valuation q 61 = true := by
  rw [value16, value36, value53, value61, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (204 : Vertex) → w ∈ [(77 : Vertex), (141 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (204 : Vertex) [(77 : Vertex), (141 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 167 = true ∨ valuation q 16 = true ∨ valuation q 36 = true ∨ valuation q 52 = true := by
  rw [value16, value36, value52, value53, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (205 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(77 : Vertex), (141 : Vertex), (204 : Vertex)] := by decide
  have hg := other_cover q (205 : Vertex) (221 : Vertex) [(77 : Vertex), (141 : Vertex), (204 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 39 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value39, value54, value55, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (209 : Vertex) (145 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 169 = true ∨ valuation q 57 = true ∨ valuation q 61 = true := by
  rw [value55, value57, value61, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (209 : Vertex) → w ∈ [(215 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (209 : Vertex) [(215 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 169 = true ∨ valuation q 54 = true ∨ valuation q 61 = true := by
  rw [value54, value55, value61, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(209 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (215 : Vertex) [(209 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 169 = true ∨ valuation q 54 = true ∨ valuation q 57 = true := by
  rw [value54, value55, value57, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (213 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(209 : Vertex), (215 : Vertex)] := by decide
  have hg := other_cover q (213 : Vertex) (221 : Vertex) [(209 : Vertex), (215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 170 = true ∨ valuation q 57 = true := by
  rw [value56, value57, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (198 : Vertex) → w ∈ [(215 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (198 : Vertex) [(215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 170 = true ∨ valuation q 49 = true := by
  rw [value49, value56, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (214 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(198 : Vertex)] := by decide
  have hg := other_cover q (214 : Vertex) (215 : Vertex) [(198 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 171 = true ∨ valuation q 56 = true := by
  rw [value56, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(214 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (213 : Vertex) [(214 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 171 = true ∨ valuation q 55 = true := by
  rw [value55, value57, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (215 : Vertex) w → w ∈ region → w ≠ (214 : Vertex) → w ∈ [(213 : Vertex)] := by decide
  have hg := other_cover q (215 : Vertex) (214 : Vertex) [(213 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value23, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (216 : Vertex) (88 : Vertex) (217 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 172 = true ∨ valuation q 23 = true ∨ valuation q 59 = true := by
  rw [value23, value58, value59, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (216 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(88 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (216 : Vertex) (218 : Vertex) [(88 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 173 = true ∨ valuation q 54 = true ∨ valuation q 58 = true := by
  rw [value54, value58, value59, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (217 : Vertex) w → w ∈ region → w ≠ (221 : Vertex) → w ∈ [(209 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (217 : Vertex) (221 : Vertex) [(209 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 174 = true ∨ valuation q 50 = true ∨ valuation q 58 = true := by
  rw [value50, value58, value60, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (90 : Vertex) → w ∈ [(202 : Vertex), (216 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (90 : Vertex) [(202 : Vertex), (216 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 174 = true ∨ valuation q 24 = true ∨ valuation q 50 = true := by
  rw [value24, value50, value60, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (218 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(90 : Vertex), (202 : Vertex)] := by decide
  have hg := other_cover q (218 : Vertex) (216 : Vertex) [(90 : Vertex), (202 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 59 = false := by
  rw [value53, value55, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (205 : Vertex) (213 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 175 = true ∨ valuation q 53 = true ∨ valuation q 59 = true := by
  rw [value53, value59, value61, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (221 : Vertex) w → w ∈ region → w ≠ (213 : Vertex) → w ∈ [(205 : Vertex), (217 : Vertex)] := by decide
  have hg := other_cover q (221 : Vertex) (213 : Vertex) [(205 : Vertex), (217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 176 = true ∨ valuation q 94 = true := by
  rw [value62, value94, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (291 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(419 : Vertex)] := by decide
  have hg := other_cover q (291 : Vertex) (299 : Vertex) [(419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 177 = true ∨ valuation q 64 = true := by
  rw [value63, value64, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (298 : Vertex) w → w ∈ region → w ≠ (314 : Vertex) → w ∈ [(299 : Vertex)] := by decide
  have hg := other_cover q (298 : Vertex) (314 : Vertex) [(299 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block7 (q : Snake 81) (h : Conditions q) : B112E146.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112146
