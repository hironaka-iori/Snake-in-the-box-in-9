import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value45, value46, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (165 : Vertex) (417 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 53 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value45, value53, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (177 : Vertex) (417 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value50, value51, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value51, value61, value99, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (175 : Vertex) (191 : Vertex) (431 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value52, value53, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value53, value55, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (179 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 78 = false ∨ valuation q 88 = false ∨ valuation q 100 = false := by
  rw [value70, value78, value88, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (289 : Vertex) (305 : Vertex) (417 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value71, value72, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (294 : Vertex) (295 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value74, value75, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (297 : Vertex) (299 : Vertex) (301 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value78, value80, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 86 = false := by
  rw [value79, value82, value83, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (306 : Vertex) (310 : Vertex) (314 : Vertex) (318 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value87, value89, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (418 : Vertex) (420 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value87, value89, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (418 : Vertex) (424 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value87, value94, value110, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (424 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 91 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value88, value91, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (421 : Vertex) (433 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 100 = false ∨ valuation q 111 = false ∨ valuation q 119 = false := by
  rw [value88, value100, value111, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (433 : Vertex) (481 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 98 = false := by
  rw [value89, value92, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (422 : Vertex) (426 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value90, value91, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (436 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value90, value92, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value92, value93, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (422 : Vertex) (423 : Vertex) (486 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 99 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value93, value99, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (439 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value94, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value100, value101, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value100, value101, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value101, value104, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value105, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 122 = false ∨ valuation q 123 = false ∨ valuation q 126 = false := by
  rw [value120, value122, value123, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (498 : Vertex) (502 : Vertex) (506 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E121.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h⟩

end
end Snake9.Regrowth.E112121
