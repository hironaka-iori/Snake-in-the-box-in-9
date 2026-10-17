import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 74 = false := by
  rw [value68, value69, value70, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (247 : Vertex) (243 : Vertex) (245 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 49 = true ∨ valuation q 69 = true ∨ valuation q 74 = true := by
  rw [value49, value69, value70, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (243 : Vertex) → w ∈ [(183 : Vertex), (245 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (243 : Vertex) [(183 : Vertex), (245 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 49 = true ∨ valuation q 68 = true ∨ valuation q 74 = true := by
  rw [value49, value68, value70, value74, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (245 : Vertex) → w ∈ [(183 : Vertex), (243 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (245 : Vertex) [(183 : Vertex), (243 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 190 = true ∨ valuation q 49 = true ∨ valuation q 68 = true ∨ valuation q 69 = true := by
  rw [value49, value68, value69, value70, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (247 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(183 : Vertex), (243 : Vertex), (245 : Vertex)] := by decide
  have hg := other_cover q (247 : Vertex) (255 : Vertex) [(183 : Vertex), (243 : Vertex), (245 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 29 = false ∨ valuation q 50 = false ∨ valuation q 66 = false := by
  rw [value29, value50, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (248 : Vertex) (120 : Vertex) (184 : Vertex) (240 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 50 = true ∨ valuation q 66 = true ∨ valuation q 72 = true := by
  rw [value50, value66, value71, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(184 : Vertex), (240 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (120 : Vertex) [(184 : Vertex), (240 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 29 = true ∨ valuation q 66 = true ∨ valuation q 72 = true := by
  rw [value29, value66, value71, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(120 : Vertex), (240 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (184 : Vertex) [(120 : Vertex), (240 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 29 = true ∨ valuation q 50 = true ∨ valuation q 72 = true := by
  rw [value29, value50, value71, value72, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (240 : Vertex) → w ∈ [(120 : Vertex), (184 : Vertex), (249 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (240 : Vertex) [(120 : Vertex), (184 : Vertex), (249 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 191 = true ∨ valuation q 29 = true ∨ valuation q 50 = true ∨ valuation q 66 = true := by
  rw [value29, value50, value66, value71, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (248 : Vertex) w → w ∈ region → w ≠ (249 : Vertex) → w ∈ [(120 : Vertex), (184 : Vertex), (240 : Vertex)] := by decide
  have hg := other_cover q (248 : Vertex) (249 : Vertex) [(120 : Vertex), (184 : Vertex), (240 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 67 = false := by
  rw [value51, value61, value67, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (233 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 71 = false := by
  rw [value51, value61, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (233 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 51 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value51, value67, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (185 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value61, value67, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (249 : Vertex) (233 : Vertex) (241 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 55 = false ∨ valuation q 65 = false ∨ valuation q 74 = false := by
  rw [value55, value65, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (254 : Vertex) (190 : Vertex) (238 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 193 = true ∨ valuation q 65 = true ∨ valuation q 74 = true := by
  rw [value65, value73, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(238 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (190 : Vertex) [(238 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 193 = true ∨ valuation q 55 = true ∨ valuation q 74 = true := by
  rw [value55, value73, value74, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(190 : Vertex), (255 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (238 : Vertex) [(190 : Vertex), (255 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 193 = true ∨ valuation q 55 = true ∨ valuation q 65 = true := by
  rw [value55, value65, value73, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (254 : Vertex) w → w ∈ region → w ≠ (255 : Vertex) → w ∈ [(190 : Vertex), (238 : Vertex)] := by decide
  have hg := other_cover q (254 : Vertex) (255 : Vertex) [(190 : Vertex), (238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 56 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value56, value70, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (255 : Vertex) (191 : Vertex) (247 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 194 = true ∨ valuation q 56 = true ∨ valuation q 73 = true := by
  rw [value56, value73, value74, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (247 : Vertex) → w ∈ [(191 : Vertex), (254 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (247 : Vertex) [(191 : Vertex), (254 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 194 = true ∨ valuation q 56 = true ∨ valuation q 70 = true := by
  rw [value56, value70, value74, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (255 : Vertex) w → w ∈ region → w ≠ (254 : Vertex) → w ∈ [(191 : Vertex), (247 : Vertex)] := by decide
  have hg := other_cover q (255 : Vertex) (254 : Vertex) [(191 : Vertex), (247 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = true := by
  rw [value75, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (301 : Vertex) w → w ∈ region → w ∈ [(303 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (301 : Vertex) [(303 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 75 = true := by
  rw [value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value75, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (303 : Vertex) (301 : Vertex) (319 : Vertex) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 196 = true ∨ valuation q 78 = true := by
  rw [value76, value78, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (303 : Vertex) w → w ∈ region → w ≠ (301 : Vertex) → w ∈ [(319 : Vertex)] := by decide
  have hg := other_cover q (303 : Vertex) (301 : Vertex) [(319 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 101 = false := by
  rw [value77, value78, value83, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (315 : Vertex) (319 : Vertex) (379 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value78, value83, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (315 : Vertex) (319 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 197 = true ∨ valuation q 83 = true ∨ valuation q 101 = true := by
  rw [value77, value83, value101, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (319 : Vertex) → w ∈ [(379 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (319 : Vertex) [(379 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 197 = true ∨ valuation q 78 = true ∨ valuation q 101 = true := by
  rw [value77, value78, value101, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (315 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(319 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (315 : Vertex) (379 : Vertex) [(319 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 16 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value16, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (319 : Vertex) (63 : Vertex) (303 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 198 = true ∨ valuation q 16 = true ∨ valuation q 77 = true := by
  rw [value16, value77, value78, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (319 : Vertex) w → w ∈ region → w ≠ (303 : Vertex) → w ∈ [(63 : Vertex), (315 : Vertex)] := by decide
  have hg := other_cover q (319 : Vertex) (303 : Vertex) [(63 : Vertex), (315 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value21, value79, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (104 : Vertex) (361 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 80 = false ∨ valuation q 109 = false := by
  rw [value21, value79, value80, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (104 : Vertex) (361 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E004.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112004
