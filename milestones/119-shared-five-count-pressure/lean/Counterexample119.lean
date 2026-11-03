import LocalWindowTags
import LocalWindowBridge
namespace Snake9.Counterexample119
open Snake9.LocalWindow
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private def values : Array Nat := #[262, 258, 266, 267, 265, 269, 268, 396, 398, 399, 391, 387, 385, 384, 448, 192, 193, 195, 199, 207, 206, 222, 254, 246, 244, 116, 124, 120, 248, 216, 217, 221, 477, 469, 468, 404, 276, 20, 21, 29, 25, 24, 8, 0, 1, 3, 7, 15, 14, 30, 286, 287, 279, 275, 273, 337, 321, 323, 327, 335, 334, 366, 302, 303, 295, 291, 289, 288, 296, 312, 314, 58, 42, 43, 41, 45, 37, 36, 38, 54, 55, 51, 49, 113, 97, 99, 103, 111, 127, 95, 87, 86, 70, 68, 69, 77, 73, 75, 74, 90, 346, 474, 475, 459, 491, 489, 505, 497, 496, 368, 370, 354, 482, 418, 434, 438, 446, 447, 445, 437, 309, 373, 375, 503, 487, 485, 484, 492, 236, 172, 174, 175, 167, 163, 161, 160, 176, 144, 145, 147, 151, 150, 134, 130, 138, 139, 137, 141, 133]
private def vertex (i : Fin 149) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩

theorem distinct : ∀ i j : Fin 149, vertex i = vertex j → i = j := by
  decide +kernel
#print axioms distinct

theorem induced : ∀ i j : Fin 149, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by
  decide +kernel
#print axioms induced

def witness : Snake 148 := ⟨vertex, distinct, induced⟩

theorem window_directions : ∀ j : Fin 6,
    dir witness (43+j.val) = ([0,1,2,3,0,4] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
#print axioms window_directions

theorem counts : coreAlpha witness 44 = 3 ∧ coreAlpha witness 45 = 6 ∧
    coreAlpha witness 46 = 3 ∧ coreAlpha witness 47 = 4 ∧ coreAlpha witness 48 = 6 := by
  decide +kernel
#print axioms counts

theorem total : coreAlpha witness 44+coreAlpha witness 45+
    coreAlpha witness 46+coreAlpha witness 47+coreAlpha witness 48 = 22 := by
  rcases counts with ⟨h1,h2,h3,h4,h5⟩
  omega
#print axioms total

theorem counterexample : ∃ p : Snake 148,
    (∀ j : Fin 6, dir p (43+j.val) = ([0,1,2,3,0,4] : List Nat).getD j.val 0) ∧
    coreAlpha p 44 ≤ 4 ∧ 6 ≤ coreAlpha p 45 ∧ coreAlpha p 46 ≤ 4 ∧
    coreAlpha p 47 ≤ 4 ∧ 6 ≤ coreAlpha p 48 ∧
    coreAlpha p 44+coreAlpha p 45+coreAlpha p 46+
      coreAlpha p 47+coreAlpha p 48 < 23 := by
  refine ⟨witness,window_directions,?_,?_,?_,?_,?_,?_⟩ <;>
    rcases counts with ⟨h1,h2,h3,h4,h5⟩ <;> omega
#print axioms counterexample

theorem coefficient_limit (a c : Nat) (h : 4*a+c ≤ 120) : min a c ≤ 24 := by omega
#print axioms coefficient_limit

theorem completed_comparison_barrier (p d R : Nat) (h : 2*p ≤ 985*d) :
    (4200*d+p)*235 ≤ 1098960*d+8*p+R := by omega
#print axioms completed_comparison_barrier

theorem conditional_comparison_barrier (p d R : Nat) (h : p ≤ 512*d) :
    (4200*d+p)*234 ≤ 1098960*d+8*p+R := by omega
#print axioms conditional_comparison_barrier
end Snake9.Counterexample119
