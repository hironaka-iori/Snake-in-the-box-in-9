import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 155 = true ∨ valuation q 33 = true ∨ valuation q 106 = true := by
  rw [value32, value33, value106, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(231 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(231 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 155 = true ∨ valuation q 33 = true ∨ valuation q 36 = true := by
  rw [value32, value33, value36, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(231 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (486 : Vertex) [(231 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value16, value30, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (227 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 16 = false ∨ valuation q 30 = false ∨ valuation q 37 = false := by
  rw [value16, value30, value33, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (167 : Vertex) (227 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 107 = false := by
  rw [value34, value35, value42, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 157 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 107 = true := by
  rw [value34, value35, value42, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(233 : Vertex), (248 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (168 : Vertex) [(233 : Vertex), (248 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 42 = true ∨ valuation q 107 = true := by
  rw [value17, value34, value42, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(168 : Vertex), (248 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (233 : Vertex) [(168 : Vertex), (248 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 35 = true ∨ valuation q 107 = true := by
  rw [value17, value34, value35, value107, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(168 : Vertex), (233 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (248 : Vertex) [(168 : Vertex), (233 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 157 = true ∨ valuation q 17 = true ∨ valuation q 35 = true ∨ valuation q 42 = true := by
  rw [value17, value34, value35, value42, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(168 : Vertex), (233 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (488 : Vertex) [(168 : Vertex), (233 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 29 = false ∨ valuation q 34 = false ∨ valuation q 108 = false := by
  rw [value29, value34, value35, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (233 : Vertex) (225 : Vertex) (232 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 29 = false ∨ valuation q 34 = false := by
  rw [value29, value34, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (233 : Vertex) (225 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 34 = false ∨ valuation q 108 = false := by
  rw [value34, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (233 : Vertex) (232 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 158 = true ∨ valuation q 34 = true ∨ valuation q 108 = true := by
  rw [value34, value35, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(232 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (225 : Vertex) [(232 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 158 = true ∨ valuation q 29 = true ∨ valuation q 108 = true := by
  rw [value29, value35, value108, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(225 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (232 : Vertex) [(225 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 158 = true ∨ valuation q 29 = true ∨ valuation q 34 = true := by
  rw [value29, value34, value35, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(225 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (489 : Vertex) [(225 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 159 = true ∨ valuation q 37 = true ∨ valuation q 112 = true := by
  rw [value36, value37, value112, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (230 : Vertex) → w ∈ [(239 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (230 : Vertex) [(239 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 112 = true := by
  rw [value32, value36, value112, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (239 : Vertex) → w ∈ [(230 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (239 : Vertex) [(230 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 159 = true ∨ valuation q 32 = true ∨ valuation q 37 = true := by
  rw [value32, value36, value37, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (238 : Vertex) w → w ∈ region → w ≠ (494 : Vertex) → w ∈ [(230 : Vertex), (239 : Vertex)] := by decide
  have hg := other_cover q (238 : Vertex) (494 : Vertex) [(230 : Vertex), (239 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 46 = false := by
  rw [value33, value36, value37, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (231 : Vertex) (238 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 113 = false := by
  rw [value33, value36, value37, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (231 : Vertex) (238 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 33 = false ∨ valuation q 46 = false ∨ valuation q 113 = false := by
  rw [value33, value37, value46, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (231 : Vertex) (255 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 36 = false ∨ valuation q 46 = false ∨ valuation q 113 = false := by
  rw [value36, value37, value46, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (239 : Vertex) (238 : Vertex) (255 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 36 = false ∨ valuation q 46 = false := by
  rw [value36, value46, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (239 : Vertex) (238 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide)

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 46 = true ∨ valuation q 113 = true := by
  rw [value33, value37, value46, value113, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(231 : Vertex), (255 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (238 : Vertex) [(231 : Vertex), (255 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 160 = true ∨ valuation q 33 = true ∨ valuation q 36 = true ∨ valuation q 113 = true := by
  rw [value33, value36, value37, value113, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (239 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(231 : Vertex), (238 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (239 : Vertex) (255 : Vertex) [(231 : Vertex), (238 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value38, value39, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (240 : Vertex) (242 : Vertex) (244 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 161 = true ∨ valuation q 41 = true ∨ valuation q 42 = true := by
  rw [value38, value41, value42, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(244 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (242 : Vertex) [(244 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 161 = true ∨ valuation q 39 = true ∨ valuation q 42 = true := by
  rw [value38, value39, value42, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (244 : Vertex) → w ∈ [(242 : Vertex), (248 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (244 : Vertex) [(242 : Vertex), (248 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 161 = true ∨ valuation q 39 = true ∨ valuation q 41 = true := by
  rw [value38, value39, value41, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (240 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(242 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (240 : Vertex) (248 : Vertex) [(242 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value38, value39, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (242 : Vertex) (240 : Vertex) (243 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 162 = true ∨ valuation q 40 = true ∨ valuation q 43 = true := by
  rw [value39, value40, value43, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(243 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (240 : Vertex) [(243 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 162 = true ∨ valuation q 38 = true ∨ valuation q 43 = true := by
  rw [value38, value39, value43, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(240 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (243 : Vertex) [(240 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E097.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112097
