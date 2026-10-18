import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 148 = true ∨ valuation q 48 = true := by
  rw [value47, value48, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (220 : Vertex) w → w ∈ region → w ≠ (222 : Vertex) → w ∈ [(221 : Vertex)] := by decide
  have hg := other_cover q (220 : Vertex) (222 : Vertex) [(221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 59 = false := by
  rw [value26, value47, value48, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (220 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 26 = false ∨ valuation q 47 = false ∨ valuation q 101 = false := by
  rw [value26, value47, value48, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (220 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 26 = false ∨ valuation q 59 = false ∨ valuation q 101 = false := by
  rw [value26, value48, value59, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (93 : Vertex) (253 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 47 = false ∨ valuation q 59 = false ∨ valuation q 101 = false := by
  rw [value47, value48, value59, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (221 : Vertex) (220 : Vertex) (253 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 150 = true ∨ valuation q 46 = true := by
  rw [value46, value49, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (222 : Vertex) w → w ∈ region → w ≠ (220 : Vertex) → w ∈ [(206 : Vertex)] := by decide
  have hg := other_cover q (222 : Vertex) (220 : Vertex) [(206 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 151 = true ∨ valuation q 29 = true ∨ valuation q 52 = true := by
  rw [value29, value50, value52, value151]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [(166 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (246 : Vertex) [(166 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 152 = true ∨ valuation q 30 = true := by
  rw [value30, value51, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (232 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(168 : Vertex)] := by decide
  have hg := other_cover q (232 : Vertex) (248 : Vertex) [(168 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 33 = false ∨ valuation q 46 = false ∨ valuation q 50 = false := by
  rw [value33, value46, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (238 : Vertex) (174 : Vertex) (206 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 154 = true ∨ valuation q 37 = true ∨ valuation q 55 = true := by
  rw [value37, value53, value55, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (242 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(178 : Vertex), (246 : Vertex)] := by decide
  have hg := other_cover q (242 : Vertex) (250 : Vertex) [(178 : Vertex), (246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 155 = true := by
  rw [value54, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (244 : Vertex) w → w ∈ region → w ≠ (246 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (244 : Vertex) (246 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 156 = true ∨ valuation q 50 = true ∨ valuation q 54 = true := by
  rw [value50, value54, value55, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (246 : Vertex) w → w ∈ region → w ≠ (242 : Vertex) → w ∈ [(230 : Vertex), (244 : Vertex)] := by decide
  have hg := other_cover q (246 : Vertex) (242 : Vertex) [(230 : Vertex), (244 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 157 = true ∨ valuation q 51 = true ∨ valuation q 57 = true := by
  rw [value51, value56, value57, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(232 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (250 : Vertex) [(232 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 158 = true ∨ valuation q 59 = true := by
  rw [value57, value59, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (249 : Vertex) w → w ∈ region → w ≠ (248 : Vertex) → w ∈ [(253 : Vertex)] := by decide
  have hg := other_cover q (249 : Vertex) (248 : Vertex) [(253 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 160 = true ∨ valuation q 42 = true ∨ valuation q 48 = true := by
  rw [value42, value48, value59, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(189 : Vertex), (221 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (249 : Vertex) [(189 : Vertex), (221 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 161 = true ∨ valuation q 77 = true := by
  rw [value60, value77, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (302 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(430 : Vertex)] := by decide
  have hg := other_cover q (302 : Vertex) (366 : Vertex) [(430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 162 = true ∨ valuation q 62 = true := by
  rw [value61, value62, value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(355 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (361 : Vertex) [(355 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 163 = true ∨ valuation q 63 = true := by
  rw [value62, value63, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(359 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (353 : Vertex) [(359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 164 = true ∨ valuation q 67 = true := by
  rw [value63, value67, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (359 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(367 : Vertex)] := by decide
  have hg := other_cover q (359 : Vertex) (355 : Vertex) [(367 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 165 = true ∨ valuation q 65 = true := by
  rw [value64, value65, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(361 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (376 : Vertex) [(361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 166 = true ∨ valuation q 61 = true := by
  rw [value61, value65, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(353 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (360 : Vertex) [(353 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 167 = true ∨ valuation q 60 = true := by
  rw [value60, value66, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (367 : Vertex) → w ∈ [(302 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (367 : Vertex) [(302 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 168 = true ∨ valuation q 66 = true := by
  rw [value66, value67, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (367 : Vertex) w → w ∈ region → w ≠ (359 : Vertex) → w ∈ [(366 : Vertex)] := by decide
  have hg := other_cover q (367 : Vertex) (359 : Vertex) [(366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 70 = true := by
  rw [value68, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ∈ [(378 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (370 : Vertex) [(378 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 68 = true := by
  rw [value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 170 = true ∨ valuation q 64 = true := by
  rw [value64, value69, value170]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(360 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (378 : Vertex) [(360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 171 = true ∨ valuation q 69 = true := by
  rw [value69, value70, value171]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (378 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(376 : Vertex)] := by decide
  have hg := other_cover q (378 : Vertex) (370 : Vertex) [(376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 172 = true ∨ valuation q 72 = true := by
  rw [value71, value72, value172]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (417 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(419 : Vertex)] := by decide
  have hg := other_cover q (417 : Vertex) (425 : Vertex) [(419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 173 = true ∨ valuation q 74 = true := by
  rw [value72, value74, value173]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (419 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(423 : Vertex)] := by decide
  have hg := other_cover q (419 : Vertex) (417 : Vertex) [(423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 29 = false ∨ valuation q 74 = false ∨ valuation q 77 = false := by
  rw [value29, value73, value74, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (166 : Vertex) (423 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value73, value74, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (422 : Vertex) (423 : Vertex) (430 : Vertex) (438 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value72, value73, value74, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (423 : Vertex) (419 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E154.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112154
