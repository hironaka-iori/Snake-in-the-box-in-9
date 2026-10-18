import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 76 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value76, value78, value79, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (289 : Vertex) (295 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 85 = false := by
  rw [value77, value78, value79, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (291 : Vertex) (290 : Vertex) (295 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 96 = false := by
  rw [value78, value79, value83, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (295 : Vertex) (291 : Vertex) (303 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 78 = true ∨ valuation q 96 = true := by
  rw [value78, value79, value96, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (295 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(291 : Vertex), (359 : Vertex)] := by decide
  have hg := other_cover q (295 : Vertex) (303 : Vertex) [(291 : Vertex), (359 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 5 = false ∨ valuation q 75 = false ∨ valuation q 97 = false := by
  rw [value5, value75, value80, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (360 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 5 = false ∨ valuation q 75 = false ∨ valuation q 112 = false := by
  rw [value5, value75, value80, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (288 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 5 = false ∨ valuation q 97 = false ∨ valuation q 112 = false := by
  rw [value5, value80, value97, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (40 : Vertex) (360 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 75 = false ∨ valuation q 81 = false ∨ valuation q 112 = false := by
  rw [value75, value80, value81, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (300 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 75 = false ∨ valuation q 97 = false ∨ valuation q 112 = false := by
  rw [value75, value80, value97, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (288 : Vertex) (360 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 97 = false ∨ valuation q 112 = false := by
  rw [value80, value81, value97, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (296 : Vertex) (300 : Vertex) (360 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 81 = true ∨ valuation q 97 = true ∨ valuation q 112 = true := by
  rw [value5, value80, value81, value97, value112, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (288 : Vertex) → w ∈ [(40 : Vertex), (300 : Vertex), (360 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (288 : Vertex) [(40 : Vertex), (300 : Vertex), (360 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 5 = true ∨ valuation q 75 = true ∨ valuation q 81 = true ∨ valuation q 97 = true := by
  rw [value5, value75, value80, value81, value97, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (296 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(40 : Vertex), (288 : Vertex), (300 : Vertex), (360 : Vertex)] := by decide
  have hg := other_cover q (296 : Vertex) (424 : Vertex) [(40 : Vertex), (288 : Vertex), (300 : Vertex), (360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 9 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value9, value80, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (44 : Vertex) (296 : Vertex) (301 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 9 = false ∨ valuation q 80 = false ∨ valuation q 90 = false := by
  rw [value9, value80, value81, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (44 : Vertex) (296 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 9 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value9, value81, value82, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (44 : Vertex) (301 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value80, value81, value82, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (300 : Vertex) (296 : Vertex) (301 : Vertex) (316 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 202 = true ∨ valuation q 83 = true ∨ valuation q 91 = true := by
  rw [value82, value83, value91, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (300 : Vertex) → w ∈ [(303 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (300 : Vertex) [(303 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 202 = true ∨ valuation q 81 = true ∨ valuation q 91 = true := by
  rw [value81, value82, value91, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(300 : Vertex), (317 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (303 : Vertex) [(300 : Vertex), (317 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 202 = true ∨ valuation q 81 = true ∨ valuation q 83 = true := by
  rw [value81, value82, value83, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(300 : Vertex), (303 : Vertex)] := by decide
  have hg := other_cover q (301 : Vertex) (317 : Vertex) [(300 : Vertex), (303 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 77 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value77, value84, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (290 : Vertex) (307 : Vertex) (310 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 77 = false ∨ valuation q 85 = false ∨ valuation q 88 = false := by
  rw [value77, value84, value85, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (290 : Vertex) (307 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 77 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value77, value84, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (290 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value84, value85, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (306 : Vertex) (307 : Vertex) (310 : Vertex) (314 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 204 = true ∨ valuation q 77 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value77, value84, value85, value88, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (306 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(290 : Vertex), (307 : Vertex), (314 : Vertex)] := by decide
  have hg := other_cover q (306 : Vertex) (310 : Vertex) [(290 : Vertex), (307 : Vertex), (314 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 206 = true ∨ valuation q 90 = true := by
  rw [value86, value90, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (308 : Vertex) w → w ∈ region → w ≠ (310 : Vertex) → w ∈ [(316 : Vertex)] := by decide
  have hg := other_cover q (308 : Vertex) (310 : Vertex) [(316 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 207 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(308 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (306 : Vertex) [(308 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 207 = true ∨ valuation q 84 = true := by
  rw [value84, value87, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (310 : Vertex) w → w ∈ region → w ≠ (308 : Vertex) → w ∈ [(306 : Vertex)] := by decide
  have hg := other_cover q (310 : Vertex) (308 : Vertex) [(306 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 208 = true ∨ valuation q 89 = true ∨ valuation q 108 = true := by
  rw [value88, value89, value108, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (306 : Vertex) → w ∈ [(315 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (306 : Vertex) [(315 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 208 = true ∨ valuation q 84 = true ∨ valuation q 108 = true := by
  rw [value84, value88, value108, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (315 : Vertex) → w ∈ [(306 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (315 : Vertex) [(306 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 208 = true ∨ valuation q 84 = true ∨ valuation q 89 = true := by
  rw [value84, value88, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (314 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(306 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (314 : Vertex) (378 : Vertex) [(306 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 109 = false := by
  rw [value85, value88, value89, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (307 : Vertex) (314 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 116 = false := by
  rw [value85, value88, value89, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (307 : Vertex) (314 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E040.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112040
