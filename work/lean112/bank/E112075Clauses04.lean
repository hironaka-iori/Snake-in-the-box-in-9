import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value78, value79, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (429 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 97 = false := by
  rw [value78, value79, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (429 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 97 = false := by
  rw [value78, value80, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (427 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 97 = false := by
  rw [value79, value80, value81, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (429 : Vertex) (430 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 186 = true ∨ valuation q 39 = true ∨ valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 97 = true := by
  rw [value39, value76, value78, value79, value81, value97, value186]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(175 : Vertex), (423 : Vertex), (427 : Vertex), (429 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (430 : Vertex) [(175 : Vertex), (423 : Vertex), (427 : Vertex), (429 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value72, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (434 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 187 = true ∨ valuation q 72 = true ∨ valuation q 85 = true := by
  rw [value72, value82, value85, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(416 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (434 : Vertex) [(416 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 187 = true ∨ valuation q 72 = true ∨ valuation q 83 = true := by
  rw [value72, value82, value83, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(416 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (440 : Vertex) [(416 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value82, value83, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (432 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 189 = true ∨ valuation q 83 = true := by
  rw [value83, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(434 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (419 : Vertex) [(434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 189 = true ∨ valuation q 74 = true := by
  rw [value74, value84, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (435 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(419 : Vertex)] := by decide
  have hg := other_cover q (435 : Vertex) (434 : Vertex) [(419 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value82, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (432 : Vertex) (442 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 103 = false := by
  rw [value83, value85, value86, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (440 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 83 = false ∨ valuation q 89 = false ∨ valuation q 103 = false := by
  rw [value83, value86, value89, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (446 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value85, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (440 : Vertex) (445 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 192 = true ∨ valuation q 88 = true ∨ valuation q 89 = true := by
  rw [value87, value88, value89, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(445 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (440 : Vertex) [(445 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 192 = true ∨ valuation q 85 = true ∨ valuation q 89 = true := by
  rw [value85, value87, value89, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(440 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (445 : Vertex) [(440 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 192 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value85, value87, value88, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(440 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (446 : Vertex) [(440 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 87 = false := by
  rw [value44, value79, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (189 : Vertex) (429 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 80 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value80, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (430 : Vertex) (442 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 61 = false ∨ valuation q 72 = false ∨ valuation q 94 = false := by
  rw [value61, value72, value90, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (416 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 61 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value61, value90, value91, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (352 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 195 = true ∨ valuation q 61 = true ∨ valuation q 72 = true ∨ valuation q 94 = true := by
  rw [value61, value72, value90, value94, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(352 : Vertex), (416 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(352 : Vertex), (416 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 195 = true ∨ valuation q 61 = true ∨ valuation q 72 = true ∨ valuation q 91 = true := by
  rw [value61, value72, value90, value91, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(352 : Vertex), (416 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(352 : Vertex), (416 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 62 = false ∨ valuation q 73 = false ∨ valuation q 90 = false := by
  rw [value62, value73, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (353 : Vertex) (417 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 196 = true ∨ valuation q 62 = true ∨ valuation q 73 = true ∨ valuation q 98 = true := by
  rw [value62, value73, value91, value98, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(353 : Vertex), (417 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(353 : Vertex), (417 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 197 = true ∨ valuation q 96 = true ∨ valuation q 101 = true := by
  rw [value92, value96, value101, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(494 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (487 : Vertex) [(494 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 197 = true ∨ valuation q 93 = true ∨ valuation q 96 = true := by
  rw [value92, value93, value96, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(487 : Vertex), (494 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (502 : Vertex) [(487 : Vertex), (494 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 65 = false ∨ valuation q 76 = false ∨ valuation q 92 = false := by
  rw [value65, value76, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (423 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 65 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value65, value92, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (359 : Vertex) (486 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 76 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value76, value92, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (487 : Vertex) (423 : Vertex) (486 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 198 = true ∨ valuation q 65 = true ∨ valuation q 76 = true ∨ valuation q 97 = true := by
  rw [value65, value76, value93, value97, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (487 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(359 : Vertex), (423 : Vertex), (495 : Vertex)] := by decide
  have hg := other_cover q (487 : Vertex) (486 : Vertex) [(359 : Vertex), (423 : Vertex), (495 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E075.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112075
