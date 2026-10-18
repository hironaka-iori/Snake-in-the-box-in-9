import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec62 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1985 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value57, value58, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (195 : Vertex) (198 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1986 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value57, value58, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (195 : Vertex) (210 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1987 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 71 = false ∨ valuation q 73 = false := by
  rw [value57, value60, value71, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (198 : Vertex) (210 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1988 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 61 = false ∨ valuation q 64 = false ∨ valuation q 68 = false := by
  rw [value58, value61, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (195 : Vertex) (199 : Vertex) (203 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1989 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 61 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value59, value61, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1990 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 61 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value60, value61, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1991 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 67 = false ∨ valuation q 73 = false ∨ valuation q 78 = false := by
  rw [value60, value67, value73, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (206 : Vertex) (214 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1992 (q : Snake 81) (h : Conditions q) : valuation q 60 = false ∨ valuation q 67 = false ∨ valuation q 111 = false ∨ valuation q 114 = false := by
  rw [value60, value67, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (206 : Vertex) (454 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1993 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value62, value63, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (201 : Vertex) (204 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1994 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value62, value63, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (201 : Vertex) (456 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1995 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 74 = false ∨ valuation q 76 = false := by
  rw [value62, value65, value74, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (204 : Vertex) (216 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1996 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 74 = false ∨ valuation q 112 = false ∨ valuation q 120 = false := by
  rw [value62, value74, value112, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (216 : Vertex) (456 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1997 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value63, value64, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (201 : Vertex) (203 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1998 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value65, value66, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (205 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1999 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value65, value67, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2000 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value67, value68, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (206 : Vertex) (207 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2001 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value69, value70, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (209 : Vertex) (210 : Vertex) (211 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2002 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value69, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (208 : Vertex) (210 : Vertex) (216 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2003 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 78 = false := by
  rw [value71, value73, value75, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (214 : Vertex) (218 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2004 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value74, value75, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (216 : Vertex) (218 : Vertex) (220 : Vertex) (222 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2005 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value74, value75, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (216 : Vertex) (218 : Vertex) (472 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2006 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value91, value92, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (387 : Vertex) (394 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2007 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value97, value98, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (397 : Vertex) (412 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2008 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value107, value108, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (449 : Vertex) (456 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2009 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value107, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (450 : Vertex) (452 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2010 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 119 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value116, value119, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (467 : Vertex) (471 : Vertex) (475 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2011 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 119 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value118, value119, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (469 : Vertex) (471 : Vertex) (477 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block62 (q : Snake 81) (h : Conditions q) : B112E089.Block62 (valuation q) :=
  ⟨clause1985 q h, clause1986 q h, clause1987 q h, clause1988 q h, clause1989 q h, clause1990 q h, clause1991 q h, clause1992 q h, clause1993 q h, clause1994 q h, clause1995 q h, clause1996 q h, clause1997 q h, clause1998 q h, clause1999 q h, clause2000 q h, clause2001 q h, clause2002 q h, clause2003 q h, clause2004 q h, clause2005 q h, clause2006 q h, clause2007 q h, clause2008 q h, clause2009 q h, clause2010 q h, clause2011 q h⟩

end
end Snake9.Regrowth.E112089
