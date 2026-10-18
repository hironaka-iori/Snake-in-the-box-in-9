import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value101, value102, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (452 : Vertex) (453 : Vertex) (460 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 217 = true ∨ valuation q 102 = true ∨ valuation q 109 = true := by
  rw [value101, value102, value109, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (452 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(453 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (452 : Vertex) (460 : Vertex) [(453 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 218 = true ∨ valuation q 80 = true ∨ valuation q 101 = true ∨ valuation q 110 = true := by
  rw [value80, value101, value102, value110, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (197 : Vertex) → w ∈ [(389 : Vertex), (452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (197 : Vertex) [(389 : Vertex), (452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 218 = true ∨ valuation q 29 = true ∨ valuation q 101 = true ∨ valuation q 110 = true := by
  rw [value29, value101, value102, value110, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (453 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(197 : Vertex), (452 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (453 : Vertex) (389 : Vertex) [(197 : Vertex), (452 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 65 = false ∨ valuation q 82 = false ∨ valuation q 114 = false := by
  rw [value65, value82, value103, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (457 : Vertex) (329 : Vertex) (393 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 220 = true ∨ valuation q 83 = true ∨ valuation q 99 = true ∨ valuation q 105 = true := by
  rw [value83, value99, value104, value105, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(394 : Vertex), (450 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (462 : Vertex) [(394 : Vertex), (450 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value100, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (458 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value100, value103, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (457 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 100 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value100, value104, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (451 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 115 = false := by
  rw [value103, value104, value105, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (459 : Vertex) (457 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 222 = true ∨ valuation q 101 = true ∨ valuation q 107 = true := by
  rw [value101, value106, value107, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (396 : Vertex) → w ∈ [(452 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (396 : Vertex) [(452 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 222 = true ∨ valuation q 84 = true ∨ valuation q 107 = true := by
  rw [value84, value106, value107, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(396 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (452 : Vertex) [(396 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 222 = true ∨ valuation q 84 = true ∨ valuation q 101 = true := by
  rw [value84, value101, value106, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(396 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (462 : Vertex) [(396 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value86, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (462 : Vertex) (398 : Vertex) (458 : Vertex) (460 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 223 = true ∨ valuation q 86 = true ∨ valuation q 104 = true := by
  rw [value86, value104, value107, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(398 : Vertex), (458 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (460 : Vertex) [(398 : Vertex), (458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 88 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value88, value108, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (400 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 224 = true ∨ valuation q 88 = true ∨ valuation q 113 = true := by
  rw [value88, value108, value113, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(400 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(400 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 224 = true ∨ valuation q 88 = true ∨ valuation q 109 = true := by
  rw [value88, value108, value109, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(400 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(400 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value101, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value101, value109, value110, value111, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(452 : Vertex), (469 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(452 : Vertex), (469 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 225 = true ∨ valuation q 101 = true ∨ valuation q 108 = true ∨ valuation q 110 = true := by
  rw [value101, value108, value109, value110, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(452 : Vertex), (464 : Vertex), (469 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (470 : Vertex) [(452 : Vertex), (464 : Vertex), (469 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 102 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value102, value109, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (453 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 226 = true ∨ valuation q 102 = true ∨ valuation q 109 = true := by
  rw [value102, value109, value110, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (469 : Vertex) w → w ∈ region → w ≠ (471 : Vertex) → w ∈ [(453 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (469 : Vertex) (471 : Vertex) [(453 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 38 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value38, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 71 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value71, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (342 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 92 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value92, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (406 : Vertex) (468 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 228 = true ∨ valuation q 111 = true ∨ valuation q 116 = true := by
  rw [value111, value112, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(470 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (469 : Vertex) [(470 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 228 = true ∨ valuation q 110 = true ∨ valuation q 116 = true := by
  rw [value110, value112, value116, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(469 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (470 : Vertex) [(469 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 228 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value110, value111, value112, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(469 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (479 : Vertex) [(469 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 229 = true ∨ valuation q 108 = true ∨ valuation q 114 = true := by
  rw [value108, value113, value114, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(464 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (408 : Vertex) [(464 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 229 = true ∨ valuation q 93 = true ∨ valuation q 114 = true := by
  rw [value93, value113, value114, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(408 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(408 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 229 = true ∨ valuation q 93 = true ∨ valuation q 108 = true := by
  rw [value93, value108, value113, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(408 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (473 : Vertex) [(408 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block9 (q : Snake 81) (h : Conditions q) : B112E120.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112120
