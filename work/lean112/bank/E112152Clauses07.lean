import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 214 = true ∨ valuation q 83 = true ∨ valuation q 95 = true := by
  rw [value83, value94, value95, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(424 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (432 : Vertex) [(424 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 214 = true ∨ valuation q 83 = true ∨ valuation q 89 = true := by
  rw [value83, value89, value94, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(424 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (442 : Vertex) [(424 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value90, value94, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (442 : Vertex) (434 : Vertex) (440 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 215 = true ∨ valuation q 90 = true ∨ valuation q 94 = true := by
  rw [value90, value94, value95, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(434 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (443 : Vertex) [(434 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 216 = true ∨ valuation q 95 = true ∨ valuation q 97 = true := by
  rw [value95, value96, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 216 = true ∨ valuation q 85 = true ∨ valuation q 97 = true := by
  rw [value85, value96, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(427 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 216 = true ∨ valuation q 85 = true ∨ valuation q 95 = true := by
  rw [value85, value95, value96, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 88 = false ∨ valuation q 96 = false ∨ valuation q 120 = false := by
  rw [value88, value96, value97, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (443 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 217 = true ∨ valuation q 88 = true ∨ valuation q 120 = true := by
  rw [value88, value97, value120, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(431 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(431 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value98, value99, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (481 : Vertex) (482 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value98, value99, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(481 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(481 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 43 = false ∨ valuation q 61 = false ∨ valuation q 98 = false := by
  rw [value43, value61, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (225 : Vertex) (353 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 43 = false ∨ valuation q 61 = false ∨ valuation q 110 = false := by
  rw [value43, value61, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (225 : Vertex) (353 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 61 = false ∨ valuation q 98 = false ∨ valuation q 110 = false := by
  rw [value61, value98, value99, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (353 : Vertex) (480 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 78 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value78, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (480 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 78 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value78, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (483 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value98, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (480 : Vertex) (483 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value98, value100, value101, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (480 : Vertex) (483 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value98, value100, value103, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (480 : Vertex) (486 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value100, value101, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (483 : Vertex) (486 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 111 = false := by
  rw [value100, value103, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (482 : Vertex) (486 : Vertex) (490 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 220 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value98, value100, value101, value105, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (490 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (486 : Vertex) [(480 : Vertex), (483 : Vertex), (490 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 220 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 111 = true := by
  rw [value98, value100, value101, value103, value111, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (486 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (490 : Vertex) [(480 : Vertex), (483 : Vertex), (486 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 220 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 105 = true := by
  rw [value98, value100, value101, value103, value105, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(480 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (498 : Vertex) [(480 : Vertex), (483 : Vertex), (486 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 79 = false := by
  rw [value44, value62, value79, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 99 = false := by
  rw [value44, value62, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value44, value62, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 62 = false ∨ valuation q 112 = false := by
  rw [value44, value62, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (355 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 100 = false := by
  rw [value44, value79, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (419 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 79 = false ∨ valuation q 112 = false := by
  rw [value44, value79, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (419 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value44, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (481 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 44 = false ∨ valuation q 99 = false ∨ valuation q 112 = false := by
  rw [value44, value99, value101, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (483 : Vertex) (227 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block7 (q : Snake 81) (h : Conditions q) : B112E152.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112152
