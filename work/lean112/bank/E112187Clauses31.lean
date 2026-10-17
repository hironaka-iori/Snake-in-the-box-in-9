import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 32 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value28, value32, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value33, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (173 : Vertex) (175 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value34, value36, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (175 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value37, value39, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (179 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 44 = false := by
  rw [value38, value40, value41, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (178 : Vertex) (182 : Vertex) (186 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value45, value46, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value45, value46, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (416 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 49 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value45, value49, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (296 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 93 = false := by
  rw [value46, value54, value81, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (289 : Vertex) (305 : Vertex) (417 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value50, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (297 : Vertex) (299 : Vertex) (301 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value51, value53, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (303 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value54, value56, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value57, value58, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (308 : Vertex) (310 : Vertex) (316 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value64, value66, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (356 : Vertex) (358 : Vertex) (364 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value65, value67, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (357 : Vertex) (359 : Vertex) (373 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 84 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value81, value84, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value83, value84, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value83, value84, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (436 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value83, value85, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value87, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 92 = false := by
  rw [value88, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value88, value89, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value89, value92, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (427 : Vertex) (431 : Vertex) (491 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value94, value97, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E187.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h⟩

end
end Snake9.Regrowth.E112187
