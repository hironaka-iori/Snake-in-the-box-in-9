import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 68 = false := by
  rw [value46, value49, value50, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (296 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value46, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 51 = false ∨ valuation q 68 = false := by
  rw [value46, value50, value51, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (299 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 46 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value46, value50, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (289 : Vertex) (301 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value49, value50, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (296 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 68 = false := by
  rw [value49, value50, value51, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (296 : Vertex) (299 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value49, value50, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (296 : Vertex) (301 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 68 = false := by
  rw [value50, value51, value52, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (297 : Vertex) (299 : Vertex) (301 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 169 = true ∨ valuation q 46 = true ∨ valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 68 = true := by
  rw [value46, value50, value51, value52, value68, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(289 : Vertex), (299 : Vertex), (301 : Vertex), (361 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (296 : Vertex) [(289 : Vertex), (299 : Vertex), (301 : Vertex), (361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 169 = true ∨ valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 52 = true := by
  rw [value46, value49, value50, value51, value52, value169]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (297 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(289 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex)] := by decide
  have hg := other_cover q (297 : Vertex) (361 : Vertex) [(289 : Vertex), (296 : Vertex), (299 : Vertex), (301 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 51 = true := by
  rw [value51, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (299 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 89 = true := by
  rw [value50, value51, value53, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ∈ [(297 : Vertex), (303 : Vertex), (427 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (299 : Vertex) [(297 : Vertex), (303 : Vertex), (427 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 170 = true ∨ valuation q 53 = true ∨ valuation q 89 = true := by
  rw [value51, value53, value89, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(303 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (297 : Vertex) [(303 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 89 = true := by
  rw [value50, value51, value89, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(297 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (303 : Vertex) [(297 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 170 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value50, value51, value53, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (299 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(297 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (299 : Vertex) (427 : Vertex) [(297 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 52 = true := by
  rw [value52, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (301 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 61 = true := by
  rw [value50, value52, value53, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ∈ [(297 : Vertex), (303 : Vertex), (317 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (301 : Vertex) [(297 : Vertex), (303 : Vertex), (317 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 171 = true ∨ valuation q 53 = true ∨ valuation q 61 = true := by
  rw [value52, value53, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (297 : Vertex) → w ∈ [(303 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (297 : Vertex) [(303 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 171 = true ∨ valuation q 50 = true ∨ valuation q 61 = true := by
  rw [value50, value52, value61, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(297 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (303 : Vertex) [(297 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 171 = true ∨ valuation q 50 = true ∨ valuation q 53 = true := by
  rw [value50, value52, value53, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(297 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(297 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value48, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 92 = false := by
  rw [value48, value51, value53, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 92 = false := by
  rw [value48, value52, value53, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (295 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 92 = false := by
  rw [value51, value52, value53, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (303 : Vertex) (299 : Vertex) (301 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 172 = true ∨ valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 92 = true := by
  rw [value48, value51, value53, value92, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(295 : Vertex), (299 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(295 : Vertex), (299 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 93 = false := by
  rw [value46, value54, value56, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (305 : Vertex) (289 : Vertex) (307 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 173 = true ∨ valuation q 56 = true ∨ valuation q 93 = true := by
  rw [value54, value56, value93, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (289 : Vertex) → w ∈ [(307 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (289 : Vertex) [(307 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 173 = true ∨ valuation q 46 = true ∨ valuation q 93 = true := by
  rw [value46, value54, value93, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (305 : Vertex) w → w ∈ region → w ≠ (307 : Vertex) → w ∈ [(289 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (305 : Vertex) (307 : Vertex) [(289 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value55, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (307 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 56 = true := by
  rw [value56, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (307 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 54 = true ∨ valuation q 55 = true ∨ valuation q 94 = true := by
  rw [value54, value55, value56, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ∈ [(305 : Vertex), (306 : Vertex), (435 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (307 : Vertex) [(305 : Vertex), (306 : Vertex), (435 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 175 = true ∨ valuation q 55 = true ∨ valuation q 94 = true := by
  rw [value55, value56, value94, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (307 : Vertex) w → w ∈ region → w ≠ (305 : Vertex) → w ∈ [(306 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (307 : Vertex) (305 : Vertex) [(306 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E187.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112187
