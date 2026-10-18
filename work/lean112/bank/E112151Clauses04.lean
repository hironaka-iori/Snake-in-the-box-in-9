import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 79 = true ∨ valuation q 83 = true := by
  rw [value79, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ∈ [(423 : Vertex), (427 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (431 : Vertex) [(423 : Vertex), (427 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 191 = true ∨ valuation q 83 = true := by
  rw [value83, value84, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(427 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (423 : Vertex) [(427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value17, value85, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (438 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 105 = false := by
  rw [value17, value85, value87, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (438 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 17 = false ∨ valuation q 90 = false ∨ valuation q 105 = false := by
  rw [value17, value85, value90, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (442 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 105 = false := by
  rw [value85, value87, value90, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (438 : Vertex) (442 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 76 = false ∨ valuation q 87 = false ∨ valuation q 92 = false := by
  rw [value76, value86, value87, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (436 : Vertex) (420 : Vertex) (438 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 193 = true ∨ valuation q 76 = true ∨ valuation q 92 = true := by
  rw [value76, value86, value92, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(420 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (438 : Vertex) [(420 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 194 = true ∨ valuation q 85 = true ∨ valuation q 86 = true := by
  rw [value85, value86, value87, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(434 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (422 : Vertex) [(434 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 194 = true ∨ valuation q 78 = true ∨ valuation q 86 = true := by
  rw [value78, value86, value87, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(422 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (434 : Vertex) [(422 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 194 = true ∨ valuation q 78 = true ∨ valuation q 85 = true := by
  rw [value78, value85, value87, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(422 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (436 : Vertex) [(422 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 80 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value80, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 80 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value80, value88, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (441 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 80 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value80, value88, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (442 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value88, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 196 = true ∨ valuation q 88 = true ∨ valuation q 91 = true := by
  rw [value88, value89, value91, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(440 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (425 : Vertex) [(440 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 196 = true ∨ valuation q 81 = true ∨ valuation q 91 = true := by
  rw [value81, value89, value91, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(425 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (440 : Vertex) [(425 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 196 = true ∨ valuation q 81 = true ∨ valuation q 88 = true := by
  rw [value81, value88, value89, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(425 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (441 : Vertex) (443 : Vertex) [(425 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value21, value82, value85, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 106 = false := by
  rw [value21, value82, value90, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (186 : Vertex) (426 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 91 = false := by
  rw [value82, value85, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (434 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 82 = false ∨ valuation q 91 = false ∨ valuation q 106 = false := by
  rw [value82, value90, value91, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (426 : Vertex) (443 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 22 = true ∨ valuation q 83 = true ∨ valuation q 89 = true ∨ valuation q 90 = true := by
  rw [value22, value83, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ∈ [(187 : Vertex), (427 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (443 : Vertex) [(187 : Vertex), (427 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 22 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value22, value83, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (427 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 22 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value22, value83, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (427 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 22 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value22, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 83 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value83, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 198 = true ∨ valuation q 83 = true ∨ valuation q 89 = true ∨ valuation q 90 = true := by
  rw [value83, value89, value90, value91, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(427 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (187 : Vertex) [(427 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 198 = true ∨ valuation q 22 = true ∨ valuation q 83 = true ∨ valuation q 90 = true := by
  rw [value22, value83, value90, value91, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(187 : Vertex), (427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (441 : Vertex) [(187 : Vertex), (427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 107 = false := by
  rw [value86, value88, value92, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (436 : Vertex) (440 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 200 = true ∨ valuation q 95 = true := by
  rw [value93, value95, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (457 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (457 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 200 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(457 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (458 : Vertex) [(457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E151.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112151
