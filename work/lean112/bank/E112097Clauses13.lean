import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 218 = true ∨ valuation q 24 = true ∨ valuation q 85 = true ∨ valuation q 93 = true ∨ valuation q 99 = true := by
  rw [value24, value85, value93, value95, value99, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(182 : Vertex), (422 : Vertex), (434 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (502 : Vertex) [(182 : Vertex), (422 : Vertex), (434 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value86, value91, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (440 : Vertex) (424 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 91 = false ∨ valuation q 97 = false := by
  rw [value91, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (440 : Vertex) (432 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide)

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 219 = true ∨ valuation q 91 = true ∨ valuation q 97 = true := by
  rw [value91, value96, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(432 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(432 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 219 = true ∨ valuation q 86 = true ∨ valuation q 97 = true := by
  rw [value86, value96, value97, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(424 : Vertex), (444 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (432 : Vertex) [(424 : Vertex), (444 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 219 = true ∨ valuation q 86 = true ∨ valuation q 91 = true := by
  rw [value86, value91, value96, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(424 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (444 : Vertex) [(424 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value96, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (444 : Vertex) (440 : Vertex) (445 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 220 = true ∨ valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value96, value97, value98, value99, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(440 : Vertex), (445 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (428 : Vertex) [(440 : Vertex), (445 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value88, value97, value98, value99, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(428 : Vertex), (445 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (440 : Vertex) [(428 : Vertex), (445 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value88, value96, value97, value99, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(428 : Vertex), (440 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (445 : Vertex) [(428 : Vertex), (440 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 220 = true ∨ valuation q 88 = true ∨ valuation q 96 = true ∨ valuation q 98 = true := by
  rw [value88, value96, value97, value98, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (444 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(428 : Vertex), (440 : Vertex), (445 : Vertex)] := by decide
  have hg := other_cover q (444 : Vertex) (446 : Vertex) [(428 : Vertex), (440 : Vertex), (445 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value97, value98, value100, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (445 : Vertex) (444 : Vertex) (447 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value97, value100, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (445 : Vertex) (444 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide)

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 221 = true ∨ valuation q 100 = true ∨ valuation q 122 = true := by
  rw [value98, value100, value122, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(447 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (444 : Vertex) [(447 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 221 = true ∨ valuation q 97 = true ∨ valuation q 122 = true := by
  rw [value97, value98, value122, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (445 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(444 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (445 : Vertex) (447 : Vertex) [(444 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value89, value95, value97, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (430 : Vertex) (438 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value89, value95, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (430 : Vertex) (438 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 89 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value89, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (430 : Vertex) (444 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value95, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (446 : Vertex) (438 : Vertex) (444 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 222 = true ∨ valuation q 89 = true ∨ valuation q 95 = true ∨ valuation q 100 = true := by
  rw [value89, value95, value99, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (446 : Vertex) w → w ∈ region → w ≠ (444 : Vertex) → w ∈ [(430 : Vertex), (438 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (446 : Vertex) (444 : Vertex) [(430 : Vertex), (438 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value90, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (445 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 123 = false := by
  rw [value90, value98, value100, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (445 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 123 = false := by
  rw [value98, value99, value100, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (445 : Vertex) (446 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 223 = true ∨ valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 123 = true := by
  rw [value98, value99, value100, value123, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(445 : Vertex), (446 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (431 : Vertex) [(445 : Vertex), (446 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 123 = true := by
  rw [value90, value99, value100, value123, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (445 : Vertex) → w ∈ [(431 : Vertex), (446 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (445 : Vertex) [(431 : Vertex), (446 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 98 = true ∨ valuation q 123 = true := by
  rw [value90, value98, value100, value123, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (446 : Vertex) → w ∈ [(431 : Vertex), (445 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (446 : Vertex) [(431 : Vertex), (445 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value90, value98, value99, value100, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (511 : Vertex) → w ∈ [(431 : Vertex), (445 : Vertex), (446 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (511 : Vertex) [(431 : Vertex), (445 : Vertex), (446 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 224 = true ∨ valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value101, value103, value104, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(482 : Vertex), (484 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(482 : Vertex), (484 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 224 = true ∨ valuation q 102 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value101, value102, value104, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (482 : Vertex) → w ∈ [(481 : Vertex), (484 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (482 : Vertex) [(481 : Vertex), (484 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 224 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 107 = true := by
  rw [value101, value102, value103, value107, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (484 : Vertex) → w ∈ [(481 : Vertex), (482 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (484 : Vertex) [(481 : Vertex), (482 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 224 = true ∨ valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 104 = true := by
  rw [value101, value102, value103, value104, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(481 : Vertex), (482 : Vertex), (484 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(481 : Vertex), (482 : Vertex), (484 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 29 = false ∨ valuation q 65 = false ∨ valuation q 82 = false := by
  rw [value29, value65, value82, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (225 : Vertex) (353 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E097.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112097
