import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 70 = false := by
  rw [value63, value67, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (245 : Vertex) (249 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 63 = false ∨ valuation q 67 = false ∨ valuation q 122 = false := by
  rw [value63, value67, value69, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (253 : Vertex) (245 : Vertex) (249 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 122 = true := by
  rw [value67, value69, value70, value122, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(249 : Vertex), (255 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (245 : Vertex) [(249 : Vertex), (255 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 63 = true ∨ valuation q 70 = true ∨ valuation q 122 = true := by
  rw [value63, value69, value70, value122, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(245 : Vertex), (255 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (249 : Vertex) [(245 : Vertex), (255 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 63 = true ∨ valuation q 67 = true ∨ valuation q 122 = true := by
  rw [value63, value67, value69, value122, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(245 : Vertex), (249 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (255 : Vertex) [(245 : Vertex), (249 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 193 = true ∨ valuation q 63 = true ∨ valuation q 67 = true ∨ valuation q 70 = true := by
  rw [value63, value67, value69, value70, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (253 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(245 : Vertex), (249 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (253 : Vertex) (509 : Vertex) [(245 : Vertex), (249 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 124 = true := by
  rw [value65, value68, value69, value70, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ∈ [(247 : Vertex), (251 : Vertex), (253 : Vertex), (511 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (255 : Vertex) [(247 : Vertex), (251 : Vertex), (253 : Vertex), (511 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 69 = false := by
  rw [value65, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (253 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 68 = false ∨ valuation q 124 = false := by
  rw [value65, value68, value70, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (251 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 65 = false ∨ valuation q 69 = false ∨ valuation q 124 = false := by
  rw [value65, value69, value70, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (247 : Vertex) (253 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 124 = false := by
  rw [value68, value69, value70, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (251 : Vertex) (253 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 65 = true ∨ valuation q 69 = true ∨ valuation q 124 = true := by
  rw [value65, value69, value70, value124, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (251 : Vertex) → w ∈ [(247 : Vertex), (253 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (251 : Vertex) [(247 : Vertex), (253 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 194 = true ∨ valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 124 = true := by
  rw [value65, value68, value70, value124, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (253 : Vertex) → w ∈ [(247 : Vertex), (251 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (253 : Vertex) [(247 : Vertex), (251 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 15 = false ∨ valuation q 75 = false ∨ valuation q 103 = false := by
  rw [value15, value71, value75, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (353 : Vertex) (97 : Vertex) (361 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 195 = true ∨ valuation q 15 = true ∨ valuation q 103 = true := by
  rw [value15, value71, value103, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (353 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(97 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (353 : Vertex) (361 : Vertex) [(97 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 196 = true ∨ valuation q 80 = true := by
  rw [value72, value80, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (356 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (356 : Vertex) (358 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 77 = true := by
  rw [value73, value77, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (356 : Vertex) → w ∈ [(366 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (356 : Vertex) [(366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 197 = true ∨ valuation q 72 = true := by
  rw [value72, value73, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (358 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(356 : Vertex)] := by decide
  have hg := other_cover q (358 : Vertex) (366 : Vertex) [(356 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 107 = false := by
  rw [value74, value75, value76, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (361 : Vertex) (362 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 198 = true ∨ valuation q 75 = true ∨ valuation q 107 = true := by
  rw [value74, value75, value107, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(361 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (362 : Vertex) [(361 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 19 = false ∨ valuation q 74 = false ∨ valuation q 108 = false := by
  rw [value19, value74, value75, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (105 : Vertex) (360 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 71 = true ∨ valuation q 74 = true ∨ valuation q 108 = true := by
  rw [value71, value74, value75, value108, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(353 : Vertex), (360 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (105 : Vertex) [(353 : Vertex), (360 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 19 = true ∨ valuation q 74 = true ∨ valuation q 108 = true := by
  rw [value19, value74, value75, value108, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(105 : Vertex), (360 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (353 : Vertex) [(105 : Vertex), (360 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 199 = true ∨ valuation q 19 = true ∨ valuation q 71 = true ∨ valuation q 108 = true := by
  rw [value19, value71, value75, value108, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(105 : Vertex), (353 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (360 : Vertex) [(105 : Vertex), (353 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 82 = false := by
  rw [value74, value76, value77, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (360 : Vertex) (366 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 77 = true ∨ valuation q 82 = true := by
  rw [value76, value77, value82, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(366 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (360 : Vertex) [(366 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 74 = true ∨ valuation q 82 = true := by
  rw [value74, value76, value82, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(360 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (366 : Vertex) [(360 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 200 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value74, value76, value77, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(360 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (378 : Vertex) [(360 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 22 = false ∨ valuation q 73 = false ∨ valuation q 76 = false := by
  rw [value22, value73, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (110 : Vertex) (358 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 22 = true ∨ valuation q 76 = true := by
  rw [value22, value76, value77, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(110 : Vertex), (362 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (358 : Vertex) [(110 : Vertex), (362 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 201 = true ∨ valuation q 22 = true ∨ valuation q 73 = true := by
  rw [value22, value73, value77, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(110 : Vertex), (358 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (362 : Vertex) [(110 : Vertex), (358 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 26 = false ∨ valuation q 79 = false ∨ valuation q 115 = false := by
  rw [value26, value78, value79, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (370 : Vertex) (114 : Vertex) (371 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E020.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112020
