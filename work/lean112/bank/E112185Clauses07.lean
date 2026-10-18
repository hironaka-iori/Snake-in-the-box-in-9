import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec7 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause225 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 194 = true ∨ valuation q 38 = true ∨ valuation q 80 = true := by
  rw [value38, value80, value86, value194]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(176 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (436 : Vertex) [(176 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause226 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 195 = true ∨ valuation q 88 = true := by
  rw [value87, value88, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (432 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause227 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 195 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value195]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (436 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(432 : Vertex)] := by decide
  have hg := other_cover q (436 : Vertex) (437 : Vertex) [(432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause228 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 196 = true ∨ valuation q 84 = true ∨ valuation q 89 = true := by
  rw [value84, value88, value89, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(421 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (436 : Vertex) [(421 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause229 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 196 = true ∨ valuation q 84 = true ∨ valuation q 87 = true := by
  rw [value84, value87, value88, value196]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (437 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(421 : Vertex), (436 : Vertex)] := by decide
  have hg := other_cover q (437 : Vertex) (439 : Vertex) [(421 : Vertex), (436 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause230 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 88 = false ∨ valuation q 92 = false := by
  rw [value88, value92, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (439 : Vertex) (437 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide)

theorem clause231 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 197 = true ∨ valuation q 92 = true := by
  rw [value89, value92, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(447 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (437 : Vertex) [(447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause232 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 197 = true ∨ valuation q 88 = true := by
  rw [value88, value89, value197]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (439 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(437 : Vertex)] := by decide
  have hg := other_cover q (439 : Vertex) (447 : Vertex) [(437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause233 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 198 = true := by
  rw [value90, value198]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (441 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (441 : Vertex) (443 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause234 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 199 = true ∨ valuation q 85 = true ∨ valuation q 90 = true := by
  rw [value85, value90, value91, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (441 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (441 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause235 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 200 = true ∨ valuation q 47 = true ∨ valuation q 91 = true := by
  rw [value47, value91, value92, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(191 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(191 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause236 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 200 = true ∨ valuation q 47 = true ∨ valuation q 89 = true := by
  rw [value47, value89, value92, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(191 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(191 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause237 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 201 = true ∨ valuation q 97 = true := by
  rw [value93, value97, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (451 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause238 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 201 = true ∨ valuation q 94 = true := by
  rw [value93, value94, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (450 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(451 : Vertex)] := by decide
  have hg := other_cover q (450 : Vertex) (458 : Vertex) [(451 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause239 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 79 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value79, value93, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (451 : Vertex) (387 : Vertex) (450 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause240 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value93, value97, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (450 : Vertex) (459 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause241 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 208 = true ∨ valuation q 97 = true := by
  rw [value97, value100, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (462 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (462 : Vertex) (460 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause242 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value80, value101, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (400 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause243 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 75 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value75, value95, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (452 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause244 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 75 = false ∨ valuation q 95 = false ∨ valuation q 103 = false := by
  rw [value75, value95, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (452 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause245 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 75 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value75, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause246 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 95 = false ∨ valuation q 101 = false ∨ valuation q 103 = false := by
  rw [value95, value101, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause247 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 212 = true ∨ valuation q 108 = true := by
  rw [value104, value108, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (469 : Vertex) → w ∈ [(479 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (469 : Vertex) [(479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause248 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 105 = true := by
  rw [value105, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (472 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause249 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value101, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ∈ [(464 : Vertex), (473 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (472 : Vertex) [(464 : Vertex), (473 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause250 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 213 = true ∨ valuation q 101 = true := by
  rw [value101, value105, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(464 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (473 : Vertex) [(464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause251 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 214 = true ∨ valuation q 107 = true := by
  rw [value106, value107, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (472 : Vertex) → w ∈ [(475 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (472 : Vertex) [(475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause252 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 214 = true ∨ valuation q 105 = true := by
  rw [value105, value106, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (473 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(472 : Vertex)] := by decide
  have hg := other_cover q (473 : Vertex) (475 : Vertex) [(472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause253 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 98 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value98, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (473 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause254 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 215 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value98, value106, value107, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(459 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (479 : Vertex) [(459 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause255 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 216 = true ∨ valuation q 107 = true := by
  rw [value107, value108, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (479 : Vertex) w → w ∈ region → w ≠ (471 : Vertex) → w ∈ [(475 : Vertex)] := by decide
  have hg := other_cover q (479 : Vertex) (471 : Vertex) [(475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause256 (q : Snake 81) (h : Conditions q) : valuation q 109 = false := by
  rw [value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (0 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block7 (q : Snake 81) (h : Conditions q) : B112E185.Block7 (valuation q) :=
  ⟨clause225 q h, clause226 q h, clause227 q h, clause228 q h, clause229 q h, clause230 q h, clause231 q h, clause232 q h, clause233 q h, clause234 q h, clause235 q h, clause236 q h, clause237 q h, clause238 q h, clause239 q h, clause240 q h, clause241 q h, clause242 q h, clause243 q h, clause244 q h, clause245 q h, clause246 q h, clause247 q h, clause248 q h, clause249 q h, clause250 q h, clause251 q h, clause252 q h, clause253 q h, clause254 q h, clause255 q h, clause256 q h⟩

end
end Snake9.Regrowth.E112185
