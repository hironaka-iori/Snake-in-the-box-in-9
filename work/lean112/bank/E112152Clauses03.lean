import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 176 = true ∨ valuation q 52 = true ∨ valuation q 58 = true := by
  rw [value52, value56, value58, value176]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(240 : Vertex), (250 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(240 : Vertex), (250 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 22 = false ∨ valuation q 56 = false ∨ valuation q 116 = false := by
  rw [value22, value56, value57, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (248 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 22 = false ∨ valuation q 59 = false ∨ valuation q 116 = false := by
  rw [value22, value57, value59, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (121 : Vertex) (251 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 39 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value39, value56, value57, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 116 = false := by
  rw [value56, value57, value59, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (248 : Vertex) (251 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 48 = false ∨ valuation q 56 = false ∨ valuation q 59 = false := by
  rw [value48, value56, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (250 : Vertex) (234 : Vertex) (248 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 49 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value49, value57, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (251 : Vertex) (235 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 120 = false := by
  rw [value55, value59, value60, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value61, value62, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (355 : Vertex) (357 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 99 = false := by
  rw [value61, value62, value63, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (355 : Vertex) (357 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 99 = false := by
  rw [value61, value62, value65, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (355 : Vertex) (361 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 99 = false := by
  rw [value61, value63, value65, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (357 : Vertex) (361 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 181 = true ∨ valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 99 = true := by
  rw [value61, value63, value65, value99, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(357 : Vertex), (361 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (355 : Vertex) [(357 : Vertex), (361 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 61 = false ∨ valuation q 66 = false ∨ valuation q 101 = false := by
  rw [value61, value62, value66, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (355 : Vertex) (353 : Vertex) (363 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 182 = true ∨ valuation q 66 = true ∨ valuation q 101 = true := by
  rw [value62, value66, value101, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(363 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (353 : Vertex) [(363 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 182 = true ∨ valuation q 61 = true ∨ valuation q 101 = true := by
  rw [value61, value62, value101, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(353 : Vertex), (483 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (363 : Vertex) [(353 : Vertex), (483 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 182 = true ∨ valuation q 61 = true ∨ valuation q 66 = true := by
  rw [value61, value62, value66, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (355 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(353 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (355 : Vertex) (483 : Vertex) [(353 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 183 = true ∨ valuation q 68 = true ∨ valuation q 71 = true ∨ valuation q 102 = true := by
  rw [value63, value68, value71, value102, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(365 : Vertex), (373 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (353 : Vertex) [(365 : Vertex), (373 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 183 = true ∨ valuation q 61 = true ∨ valuation q 71 = true ∨ valuation q 102 = true := by
  rw [value61, value63, value71, value102, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(353 : Vertex), (373 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (365 : Vertex) [(353 : Vertex), (373 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 183 = true ∨ valuation q 61 = true ∨ valuation q 68 = true ∨ valuation q 102 = true := by
  rw [value61, value63, value68, value102, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(353 : Vertex), (365 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (373 : Vertex) [(353 : Vertex), (365 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 183 = true ∨ valuation q 61 = true ∨ valuation q 68 = true ∨ valuation q 71 = true := by
  rw [value61, value63, value68, value71, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (357 : Vertex) w → w ∈ region → w ≠ (485 : Vertex) → w ∈ [(353 : Vertex), (365 : Vertex), (373 : Vertex)] := by decide
  have hg := other_cover q (357 : Vertex) (485 : Vertex) [(353 : Vertex), (365 : Vertex), (373 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 184 = true ∨ valuation q 72 = true ∨ valuation q 103 = true := by
  rw [value64, value72, value103, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (102 : Vertex) → w ∈ [(374 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (102 : Vertex) [(374 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 184 = true ∨ valuation q 12 = true ∨ valuation q 103 = true := by
  rw [value12, value64, value103, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (374 : Vertex) → w ∈ [(102 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (374 : Vertex) [(102 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 184 = true ∨ valuation q 12 = true ∨ valuation q 72 = true := by
  rw [value12, value64, value72, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(102 : Vertex), (374 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (486 : Vertex) [(102 : Vertex), (374 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 185 = true ∨ valuation q 15 = true ∨ valuation q 61 = true ∨ valuation q 68 = true := by
  rw [value15, value61, value65, value68, value185]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(105 : Vertex), (353 : Vertex), (365 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (363 : Vertex) [(105 : Vertex), (353 : Vertex), (365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 76 = false := by
  rw [value62, value65, value66, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (355 : Vertex) (361 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 186 = true ∨ valuation q 65 = true ∨ valuation q 76 = true := by
  rw [value65, value66, value76, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (355 : Vertex) → w ∈ [(361 : Vertex), (379 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (355 : Vertex) [(361 : Vertex), (379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 186 = true ∨ valuation q 62 = true ∨ valuation q 65 = true := by
  rw [value62, value65, value66, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(355 : Vertex), (361 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (379 : Vertex) [(355 : Vertex), (361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 106 = true := by
  rw [value67, value106, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (365 : Vertex) → w ∈ [(492 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (365 : Vertex) [(492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 187 = true ∨ valuation q 68 = true := by
  rw [value67, value68, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (364 : Vertex) w → w ∈ region → w ≠ (492 : Vertex) → w ∈ [(365 : Vertex)] := by decide
  have hg := other_cover q (364 : Vertex) (492 : Vertex) [(365 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 67 = false := by
  rw [value63, value65, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (361 : Vertex) (364 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 107 = false := by
  rw [value63, value65, value68, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (365 : Vertex) (357 : Vertex) (361 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E152.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112152
