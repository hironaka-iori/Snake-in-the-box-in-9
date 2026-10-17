import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 152 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (75 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(79 : Vertex)] := by decide
  have hg := other_cover q (75 : Vertex) (107 : Vertex) [(79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 97 = true := by
  rw [value37, value97, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(207 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (75 : Vertex) [(207 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 153 = true ∨ valuation q 36 = true := by
  rw [value36, value37, value153]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (207 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (207 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 98 = true := by
  rw [value38, value98, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(208 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (84 : Vertex) [(208 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 154 = true ∨ valuation q 40 = true := by
  rw [value38, value40, value154]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (80 : Vertex) w → w ∈ region → w ≠ (208 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (80 : Vertex) (208 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 49 = true := by
  rw [value39, value49, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (87 : Vertex) → w ∈ [(115 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (87 : Vertex) [(115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 155 = true ∨ valuation q 41 = true := by
  rw [value39, value41, value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (83 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(87 : Vertex)] := by decide
  have hg := other_cover q (83 : Vertex) (115 : Vertex) [(87 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 50 = true := by
  rw [value40, value50, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (80 : Vertex) → w ∈ [(116 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (80 : Vertex) [(116 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 156 = true ∨ valuation q 38 = true := by
  rw [value38, value40, value156]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(80 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (116 : Vertex) [(80 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 101 = true := by
  rw [value41, value101, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(215 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (83 : Vertex) [(215 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 157 = true ∨ valuation q 39 = true := by
  rw [value39, value41, value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (87 : Vertex) w → w ∈ region → w ≠ (215 : Vertex) → w ∈ [(83 : Vertex)] := by decide
  have hg := other_cover q (87 : Vertex) (215 : Vertex) [(83 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 102 = true := by
  rw [value42, value102, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(217 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (93 : Vertex) [(217 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 158 = true ∨ valuation q 43 = true := by
  rw [value42, value43, value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (89 : Vertex) w → w ∈ region → w ≠ (217 : Vertex) → w ∈ [(93 : Vertex)] := by decide
  have hg := other_cover q (89 : Vertex) (217 : Vertex) [(93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 52 = true := by
  rw [value43, value52, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (89 : Vertex) → w ∈ [(125 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (89 : Vertex) [(125 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 159 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (125 : Vertex) → w ∈ [(89 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (125 : Vertex) [(89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 107 = true := by
  rw [value44, value107, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (107 : Vertex) → w ∈ [(233 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (107 : Vertex) [(233 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 160 = true ∨ valuation q 45 = true := by
  rw [value44, value45, value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (105 : Vertex) w → w ∈ region → w ≠ (233 : Vertex) → w ∈ [(107 : Vertex)] := by decide
  have hg := other_cover q (105 : Vertex) (233 : Vertex) [(107 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 161 = true ∨ valuation q 44 = true ∨ valuation q 108 = true := by
  rw [value44, value45, value108, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(105 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (75 : Vertex) [(105 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 108 = true := by
  rw [value36, value45, value108, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(75 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (105 : Vertex) [(75 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 161 = true ∨ valuation q 36 = true ∨ valuation q 44 = true := by
  rw [value36, value44, value45, value161]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (107 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(75 : Vertex), (105 : Vertex)] := by decide
  have hg := other_cover q (107 : Vertex) (235 : Vertex) [(75 : Vertex), (105 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = true := by
  rw [value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (108 : Vertex) w → w ∈ region → w ∈ [(110 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (108 : Vertex) [(110 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 46 = true := by
  rw [value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 163 = true ∨ valuation q 110 = true := by
  rw [value47, value110, value163]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (110 : Vertex) w → w ∈ region → w ≠ (108 : Vertex) → w ∈ [(238 : Vertex)] := by decide
  have hg := other_cover q (110 : Vertex) (108 : Vertex) [(238 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 49 = true := by
  rw [value48, value49, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (49 : Vertex) → w ∈ [(115 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (49 : Vertex) [(115 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 164 = true ∨ valuation q 28 = true := by
  rw [value28, value48, value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (113 : Vertex) w → w ∈ region → w ≠ (115 : Vertex) → w ∈ [(49 : Vertex)] := by decide
  have hg := other_cover q (113 : Vertex) (115 : Vertex) [(49 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 39 = false ∨ valuation q 48 = false ∨ valuation q 112 = false := by
  rw [value39, value48, value49, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (115 : Vertex) (83 : Vertex) (113 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 165 = true ∨ valuation q 48 = true ∨ valuation q 112 = true := by
  rw [value48, value49, value112, value165]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (115 : Vertex) w → w ∈ region → w ≠ (83 : Vertex) → w ∈ [(113 : Vertex), (243 : Vertex)] := by decide
  have hg := other_cover q (115 : Vertex) (83 : Vertex) [(113 : Vertex), (243 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 51 = true := by
  rw [value50, value51, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (84 : Vertex) → w ∈ [(118 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (84 : Vertex) [(118 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 166 = true ∨ valuation q 40 = true := by
  rw [value40, value50, value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (116 : Vertex) w → w ∈ region → w ≠ (118 : Vertex) → w ∈ [(84 : Vertex)] := by decide
  have hg := other_cover q (116 : Vertex) (118 : Vertex) [(84 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 167 = true ∨ valuation q 114 = true := by
  rw [value51, value114, value167]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (118 : Vertex) w → w ∈ region → w ≠ (116 : Vertex) → w ∈ [(246 : Vertex)] := by decide
  have hg := other_cover q (118 : Vertex) (116 : Vertex) [(246 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 53 = true := by
  rw [value52, value53, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (93 : Vertex) → w ∈ [(127 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (93 : Vertex) [(127 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 168 = true ∨ valuation q 43 = true := by
  rw [value43, value52, value168]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (125 : Vertex) w → w ∈ region → w ≠ (127 : Vertex) → w ∈ [(93 : Vertex)] := by decide
  have hg := other_cover q (125 : Vertex) (127 : Vertex) [(93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block6 (q : Snake 81) (h : Conditions q) : B112E259.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112259
