import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 59 = false ∨ valuation q 96 = false := by
  rw [value46, value50, value59, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (235 : Vertex) (227 : Vertex) (251 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 158 = true ∨ valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 96 = true := by
  rw [value46, value49, value50, value96, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (235 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(227 : Vertex), (234 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (235 : Vertex) (251 : Vertex) [(227 : Vertex), (234 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 159 = true ∨ valuation q 52 = true := by
  rw [value51, value52, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (228 : Vertex) → w ∈ [(238 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (228 : Vertex) [(238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 159 = true ∨ valuation q 47 = true := by
  rw [value47, value51, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (236 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(228 : Vertex)] := by decide
  have hg := other_cover q (236 : Vertex) (238 : Vertex) [(228 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 160 = true ∨ valuation q 49 = true := by
  rw [value49, value52, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (236 : Vertex) → w ∈ [(234 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (236 : Vertex) [(234 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 162 = true ∨ valuation q 47 = true ∨ valuation q 53 = true := by
  rw [value47, value53, value54, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(228 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (244 : Vertex) (245 : Vertex) [(228 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 48 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value48, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (245 : Vertex) (229 : Vertex) (244 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 163 = true ∨ valuation q 48 = true ∨ valuation q 54 = true := by
  rw [value48, value54, value55, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (245 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(229 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (245 : Vertex) (247 : Vertex) [(229 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 164 = true ∨ valuation q 60 = true := by
  rw [value56, value60, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 164 = true ∨ valuation q 55 = true := by
  rw [value55, value56, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(245 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 165 = true ∨ valuation q 26 = true ∨ valuation q 53 = true ∨ valuation q 104 = true := by
  rw [value26, value53, value57, value104, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(120 : Vertex), (240 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(120 : Vertex), (240 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 165 = true ∨ valuation q 26 = true ∨ valuation q 53 = true ∨ valuation q 58 = true := by
  rw [value26, value53, value57, value58, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(120 : Vertex), (240 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (504 : Vertex) [(120 : Vertex), (240 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 166 = true ∨ valuation q 59 = true := by
  rw [value58, value59, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(251 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(251 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 166 = true ∨ valuation q 57 = true := by
  rw [value57, value58, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(248 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (251 : Vertex) [(248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 167 = true ∨ valuation q 50 = true ∨ valuation q 58 = true := by
  rw [value50, value58, value59, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (251 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(235 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (251 : Vertex) (255 : Vertex) [(235 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 108 = false := by
  rw [value56, value59, value60, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 168 = true ∨ valuation q 59 = true ∨ valuation q 108 = true := by
  rw [value59, value60, value108, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(251 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(251 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 169 = true ∨ valuation q 62 = true := by
  rw [value61, value62, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (258 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(259 : Vertex)] := by decide
  have hg := other_cover q (258 : Vertex) (266 : Vertex) [(259 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 170 = true ∨ valuation q 77 = true := by
  rw [value62, value77, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (259 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(387 : Vertex)] := by decide
  have hg := other_cover q (259 : Vertex) (258 : Vertex) [(387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value63, value64, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (260 : Vertex) (261 : Vertex) (268 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 173 = true ∨ valuation q 67 = true := by
  rw [value65, value67, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(270 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (258 : Vertex) [(270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 173 = true ∨ valuation q 61 = true := by
  rw [value61, value65, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(258 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (270 : Vertex) [(258 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 174 = true ∨ valuation q 67 = true := by
  rw [value66, value67, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(270 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (260 : Vertex) [(270 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 174 = true ∨ valuation q 63 = true := by
  rw [value63, value66, value174]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (268 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(260 : Vertex)] := by decide
  have hg := other_cover q (268 : Vertex) (270 : Vertex) [(260 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 175 = true ∨ valuation q 65 = true := by
  rw [value65, value67, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (270 : Vertex) w → w ∈ region → w ≠ (268 : Vertex) → w ∈ [(266 : Vertex)] := by decide
  have hg := other_cover q (270 : Vertex) (268 : Vertex) [(266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 72 = false ∨ valuation q 78 = false := by
  rw [value68, value69, value72, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (280 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 63 = false ∨ valuation q 68 = false ∨ valuation q 70 = false := by
  rw [value63, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 179 = true ∨ valuation q 70 = true := by
  rw [value70, value71, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(277 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (287 : Vertex) [(277 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 180 = true ∨ valuation q 68 = true := by
  rw [value68, value72, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(272 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(272 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 181 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(280 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [(280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 182 = true ∨ valuation q 73 = true := by
  rw [value73, value74, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (283 : Vertex) w → w ∈ region → w ≠ (287 : Vertex) → w ∈ [(281 : Vertex)] := by decide
  have hg := other_cover q (283 : Vertex) (287 : Vertex) [(281 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 30 = false ∨ valuation q 62 = false ∨ valuation q 80 = false := by
  rw [value30, value62, value77, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (131 : Vertex) (259 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E190.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112190
