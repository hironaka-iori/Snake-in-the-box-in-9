import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 175 = true ∨ valuation q 73 = true ∨ valuation q 78 = true := by
  rw [value73, value74, value78, value175]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (423 : Vertex) w → w ∈ region → w ≠ (419 : Vertex) → w ∈ [(422 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (423 : Vertex) (419 : Vertex) [(422 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 30 = false ∨ valuation q 76 = false ∨ valuation q 83 = false := by
  rw [value30, value75, value76, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 177 = true ∨ valuation q 71 = true ∨ valuation q 84 = true := by
  rw [value71, value76, value84, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(417 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (424 : Vertex) [(417 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 177 = true ∨ valuation q 71 = true ∨ valuation q 75 = true := by
  rw [value71, value75, value76, value177]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(417 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (441 : Vertex) [(417 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 33 = false ∨ valuation q 60 = false ∨ valuation q 73 = false := by
  rw [value33, value60, value73, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (302 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 33 = false ∨ valuation q 60 = false ∨ valuation q 78 = false := by
  rw [value33, value60, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (302 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 33 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value33, value73, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (174 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 60 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value60, value73, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (302 : Vertex) (422 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 178 = true ∨ valuation q 33 = true ∨ valuation q 73 = true ∨ valuation q 78 = true := by
  rw [value33, value73, value77, value78, value178]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (302 : Vertex) → w ∈ [(174 : Vertex), (422 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (302 : Vertex) [(174 : Vertex), (422 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 179 = true ∨ valuation q 74 = true ∨ valuation q 77 = true := by
  rw [value74, value77, value78, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(423 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (175 : Vertex) [(423 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 179 = true ∨ valuation q 34 = true ∨ valuation q 77 = true := by
  rw [value34, value77, value78, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(175 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (423 : Vertex) [(175 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 179 = true ∨ valuation q 34 = true ∨ valuation q 74 = true := by
  rw [value34, value74, value78, value179]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(175 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (430 : Vertex) [(175 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 37 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value37, value79, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (434 : Vertex) (178 : Vertex) (438 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 180 = true ∨ valuation q 37 = true ∨ valuation q 82 = true := by
  rw [value37, value79, value82, value180]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (434 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(178 : Vertex), (438 : Vertex)] := by decide
  have hg := other_cover q (434 : Vertex) (442 : Vertex) [(178 : Vertex), (438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 181 = true ∨ valuation q 82 = true := by
  rw [value80, value82, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(438 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 181 = true ∨ valuation q 81 = true := by
  rw [value80, value81, value181]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (438 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (438 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 182 = true ∨ valuation q 39 = true := by
  rw [value39, value81, value182]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(181 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(181 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value73, value79, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (438 : Vertex) (422 : Vertex) (434 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 183 = true ∨ valuation q 73 = true ∨ valuation q 80 = true := by
  rw [value73, value80, value82, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (434 : Vertex) → w ∈ [(422 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (434 : Vertex) [(422 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 183 = true ∨ valuation q 73 = true ∨ valuation q 79 = true := by
  rw [value73, value79, value82, value183]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (438 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(422 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (438 : Vertex) (436 : Vertex) [(422 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 184 = true ∨ valuation q 75 = true ∨ valuation q 85 = true := by
  rw [value75, value83, value85, value184]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(424 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (441 : Vertex) [(424 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 187 = true ∨ valuation q 91 = true := by
  rw [value86, value91, value187]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(457 : Vertex)] := by decide
  have hg := other_cover q (449 : Vertex) (451 : Vertex) [(457 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 188 = true ∨ valuation q 89 = true := by
  rw [value87, value89, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(455 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (449 : Vertex) [(455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 188 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value188]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(449 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value88, value89, value92, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (454 : Vertex) (455 : Vertex) (462 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 189 = true ∨ valuation q 92 = true ∨ valuation q 97 = true := by
  rw [value88, value92, value97, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(462 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (455 : Vertex) [(462 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 189 = true ∨ valuation q 89 = true ∨ valuation q 97 = true := by
  rw [value88, value89, value97, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (462 : Vertex) [(455 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 190 = true ∨ valuation q 88 = true ∨ valuation q 93 = true := by
  rw [value88, value89, value93, value190]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(454 : Vertex), (463 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (451 : Vertex) [(454 : Vertex), (463 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 193 = true ∨ valuation q 46 = true ∨ valuation q 88 = true := by
  rw [value46, value88, value92, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (463 : Vertex) → w ∈ [(206 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (463 : Vertex) [(206 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 194 = true ∨ valuation q 92 = true := by
  rw [value92, value93, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(462 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (455 : Vertex) [(462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 194 = true ∨ valuation q 89 = true := by
  rw [value89, value93, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (463 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(455 : Vertex)] := by decide
  have hg := other_cover q (463 : Vertex) (462 : Vertex) [(455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 195 = true ∨ valuation q 100 = true := by
  rw [value94, value100, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(474 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (470 : Vertex) [(474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E154.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112154
