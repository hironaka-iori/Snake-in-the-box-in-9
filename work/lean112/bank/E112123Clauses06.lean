import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 189 = true ∨ valuation q 19 = true ∨ valuation q 78 = true := by
  rw [value19, value78, value79, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (287 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(31 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (287 : Vertex) (279 : Vertex) [(31 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 190 = true := by
  rw [value80, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 64 = false ∨ valuation q 84 = false ∨ valuation q 96 = false := by
  rw [value64, value81, value84, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (403 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 96 = false := by
  rw [value81, value84, value85, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (403 : Vertex) (419 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 71 = false ∨ valuation q 83 = false ∨ valuation q 88 = false := by
  rw [value71, value82, value83, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (272 : Vertex) (401 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 88 = false ∨ valuation q 103 = false := by
  rw [value82, value83, value88, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (400 : Vertex) (401 : Vertex) (432 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 193 = true ∨ valuation q 84 = true := by
  rw [value83, value84, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(403 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (400 : Vertex) [(403 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 193 = true ∨ valuation q 82 = true := by
  rw [value82, value83, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(400 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (403 : Vertex) [(400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 194 = true ∨ valuation q 81 = true := by
  rw [value81, value84, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(387 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 195 = true ∨ valuation q 81 = true := by
  rw [value81, value85, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(387 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (427 : Vertex) [(387 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 196 = true ∨ valuation q 90 = true := by
  rw [value86, value90, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (165 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 198 = true ∨ valuation q 40 = true ∨ valuation q 82 = true := by
  rw [value40, value82, value88, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(176 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (436 : Vertex) [(176 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 199 = true ∨ valuation q 90 = true := by
  rw [value89, value90, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (432 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value86, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (437 : Vertex) (421 : Vertex) (436 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 202 = true := by
  rw [value92, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (441 : Vertex) (443 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 205 = true ∨ valuation q 96 = true := by
  rw [value95, value96, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(451 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 104 = false := by
  rw [value97, value98, value101, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (453 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = true ∨ valuation q 105 = true := by
  rw [value97, value98, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ∈ [(452 : Vertex), (469 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (453 : Vertex) [(452 : Vertex), (469 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 98 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value98, value104, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 217 = true ∨ valuation q 103 = true := by
  rw [value103, value107, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(464 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (473 : Vertex) [(464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 218 = true ∨ valuation q 107 = true := by
  rw [value107, value108, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(472 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (475 : Vertex) [(472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 100 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value100, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (473 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 220 = true ∨ valuation q 109 = true := by
  rw [value109, value110, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (471 : Vertex) → w ∈ [(475 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (471 : Vertex) [(475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 111 = false := by
  rw [value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 114 = false := by
  rw [value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (3 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 115 = false := by
  rw [value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (5 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 116 = false := by
  rw [value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (6 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 119 = false := by
  rw [value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (15 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 121 = false := by
  rw [value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (17 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 122 = false := by
  rw [value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (18 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 125 = false := by
  rw [value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (24 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (29 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block6 (q : Snake 81) (h : Conditions q) : B112E123.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112123
