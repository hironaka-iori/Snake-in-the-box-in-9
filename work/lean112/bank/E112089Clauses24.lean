import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 7 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 95 = true := by
  rw [value7, value80, value81, value82, value95, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(10 : Vertex), (264 : Vertex), (282 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (330 : Vertex) [(10 : Vertex), (264 : Vertex), (282 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 7 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 86 = true := by
  rw [value7, value80, value81, value82, value86, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (266 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(10 : Vertex), (264 : Vertex), (282 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (266 : Vertex) (394 : Vertex) [(10 : Vertex), (264 : Vertex), (282 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 206 = true := by
  rw [value82, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (282 : Vertex) (266 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value79, value83, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (327 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 85 = true ∨ valuation q 87 = true := by
  rw [value83, value85, value87, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (259 : Vertex) → w ∈ [(327 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (259 : Vertex) [(327 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 87 = true := by
  rw [value79, value83, value87, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(259 : Vertex), (331 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (327 : Vertex) [(259 : Vertex), (331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 85 = true := by
  rw [value79, value83, value85, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(259 : Vertex), (327 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (331 : Vertex) [(259 : Vertex), (327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 89 = true := by
  rw [value84, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (327 : Vertex) [(333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 85 = true := by
  rw [value84, value85, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(327 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (333 : Vertex) [(327 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 84 = true := by
  rw [value84, value85, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(325 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (323 : Vertex) [(325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 83 = true := by
  rw [value83, value85, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (327 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(323 : Vertex)] := by decide
  have hg := other_cover q (327 : Vertex) (325 : Vertex) [(323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 87 = true := by
  rw [value86, value87, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (266 : Vertex) → w ∈ [(331 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (266 : Vertex) [(331 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 210 = true ∨ valuation q 81 = true := by
  rw [value81, value86, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (331 : Vertex) → w ∈ [(266 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (331 : Vertex) [(266 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 86 = true := by
  rw [value86, value87, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (323 : Vertex) → w ∈ [(330 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (323 : Vertex) [(330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 211 = true ∨ valuation q 83 = true := by
  rw [value83, value87, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (331 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(323 : Vertex)] := by decide
  have hg := other_cover q (331 : Vertex) (330 : Vertex) [(323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 25 = true ∨ valuation q 89 = true := by
  rw [value25, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ∈ [(76 : Vertex), (333 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (332 : Vertex) [(76 : Vertex), (333 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 25 = false ∨ valuation q 89 = false := by
  rw [value25, value89, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (332 : Vertex) (76 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide)

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 88 = true := by
  rw [value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 212 = true := by
  rw [value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change BallClauseLogic.Endpoint q head
  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 213 = true ∨ valuation q 84 = true := by
  rw [value84, value89, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(325 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value90, value91, value99, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (384 : Vertex) (386 : Vertex) (400 : Vertex) (448 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 214 = true ∨ valuation q 91 = true ∨ valuation q 107 = true := by
  rw [value90, value91, value107, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (384 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(386 : Vertex), (448 : Vertex)] := by decide
  have hg := other_cover q (384 : Vertex) (400 : Vertex) [(386 : Vertex), (448 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 91 = true := by
  rw [value91, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (386 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 37 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value37, value90, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (384 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 37 = false ∨ valuation q 92 = false ∨ valuation q 101 = false := by
  rw [value37, value91, value92, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (387 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 37 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value37, value91, value95, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (130 : Vertex) (394 : Vertex) (402 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 109 = false := by
  rw [value90, value91, value92, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (384 : Vertex) (387 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value91, value92, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (387 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 101 = false ∨ valuation q 109 = false := by
  rw [value91, value95, value101, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (386 : Vertex) (394 : Vertex) (402 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 37 = true ∨ valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 101 = true ∨ valuation q 109 = true := by
  rw [value37, value91, value92, value95, value101, value109, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(130 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(130 : Vertex), (387 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 215 = true ∨ valuation q 37 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 101 = true ∨ valuation q 109 = true := by
  rw [value37, value90, value91, value95, value101, value109, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(130 : Vertex), (384 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (387 : Vertex) [(130 : Vertex), (384 : Vertex), (394 : Vertex), (402 : Vertex), (450 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 79 = false ∨ valuation q 91 = false ∨ valuation q 94 = false := by
  rw [value79, value91, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (387 : Vertex) (259 : Vertex) (386 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E089.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112089
