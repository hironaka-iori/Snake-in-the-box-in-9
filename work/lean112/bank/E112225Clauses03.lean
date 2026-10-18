import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 74 = false ∨ valuation q 85 = false ∨ valuation q 98 = false := by
  rw [value74, value84, value85, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (388 : Vertex) (405 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 86 = true := by
  rw [value82, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ∈ [(401 : Vertex), (404 : Vertex), (407 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (405 : Vertex) [(401 : Vertex), (404 : Vertex), (407 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 189 = true ∨ valuation q 84 = true ∨ valuation q 86 = true := by
  rw [value84, value85, value86, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (401 : Vertex) [(404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 189 = true ∨ valuation q 82 = true ∨ valuation q 86 = true := by
  rw [value82, value85, value86, value189]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(401 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (404 : Vertex) [(401 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 76 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value76, value83, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (391 : Vertex) (403 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 191 = true ∨ valuation q 82 = true ∨ valuation q 89 = true := by
  rw [value82, value87, value89, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(401 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(401 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 191 = true ∨ valuation q 78 = true ∨ valuation q 89 = true := by
  rw [value78, value87, value89, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(393 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (401 : Vertex) [(393 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 191 = true ∨ valuation q 78 = true ∨ valuation q 82 = true := by
  rw [value78, value82, value87, value191]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(393 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(393 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 79 = true ∨ valuation q 89 = true := by
  rw [value79, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ∈ [(394 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (410 : Vertex) [(394 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value79, value89, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (410 : Vertex) (394 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide)

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 192 = true ∨ valuation q 89 = true := by
  rw [value88, value89, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(411 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (394 : Vertex) [(411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 192 = true ∨ valuation q 79 = true := by
  rw [value79, value88, value192]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(394 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (411 : Vertex) [(394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 83 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value83, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 193 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value89, value193]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(409 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (403 : Vertex) [(409 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 194 = true := by
  rw [value90, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (449 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (449 : Vertex) (451 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 91 = true := by
  rw [value91, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (451 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 97 = true := by
  rw [value90, value91, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ∈ [(449 : Vertex), (455 : Vertex), (467 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (451 : Vertex) [(449 : Vertex), (455 : Vertex), (467 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value93, value97, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (451 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide)

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 195 = true ∨ valuation q 90 = true ∨ valuation q 97 = true := by
  rw [value90, value91, value97, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(449 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (455 : Vertex) [(449 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 195 = true ∨ valuation q 90 = true ∨ valuation q 93 = true := by
  rw [value90, value91, value93, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (451 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (451 : Vertex) (467 : Vertex) [(449 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 93 = true ∨ valuation q 102 = true := by
  rw [value92, value93, value102, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(455 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (390 : Vertex) [(455 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 75 = true ∨ valuation q 102 = true := by
  rw [value75, value92, value102, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(390 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (455 : Vertex) [(390 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 196 = true ∨ valuation q 75 = true ∨ valuation q 93 = true := by
  rw [value75, value92, value93, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(390 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (486 : Vertex) [(390 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 76 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value76, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (391 : Vertex) (451 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 197 = true ∨ valuation q 91 = true ∨ valuation q 92 = true := by
  rw [value91, value92, value93, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (391 : Vertex) → w ∈ [(451 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (391 : Vertex) [(451 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 197 = true ∨ valuation q 76 = true ∨ valuation q 91 = true := by
  rw [value76, value91, value93, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(391 : Vertex), (451 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (454 : Vertex) [(391 : Vertex), (451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 103 = false := by
  rw [value77, value94, value99, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (456 : Vertex) (392 : Vertex) (472 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 198 = true ∨ valuation q 77 = true ∨ valuation q 99 = true := by
  rw [value77, value94, value99, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (456 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(392 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (456 : Vertex) (488 : Vertex) [(392 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value95, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (466 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 199 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value95, value98, value99, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (466 : Vertex) → w ∈ [(468 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (466 : Vertex) [(468 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 199 = true ∨ valuation q 96 = true ∨ valuation q 99 = true := by
  rw [value95, value96, value99, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(466 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (468 : Vertex) [(466 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 199 = true ∨ valuation q 96 = true ∨ valuation q 98 = true := by
  rw [value95, value96, value98, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(466 : Vertex), (468 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (472 : Vertex) [(466 : Vertex), (468 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block3 (q : Snake 81) (h : Conditions q) : B112E225.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112225
