import Clique

namespace Entry87.Shapes

def shapes : List (List Nat) := [[2],[3],[0,1],[0,19],[1,18]]
def touch (s t : List Nat) : Bool :=
  s.any fun x => t.any fun y => decide (Entry87.hamming x y ≤ 1)

theorem allTouch : shapes.all (fun s => shapes.all (touch s)) = true := by decide

theorem touching_subsets {a b s t : List Nat}
    (ac : a ∈ shapes) (bc : b ∈ shapes) (sa : ∀ x ∈ a, x ∈ s) (tb : ∀ x ∈ b, x ∈ t) :
    ∃ x ∈ s, ∃ y ∈ t, Entry87.hamming x y ≤ 1 := by
  have ha := List.all_eq_true.mp allTouch a ac
  have hb := List.all_eq_true.mp ha b bc
  simp [touch] at hb
  obtain ⟨x,hx,y,hy,dist⟩ := hb
  exact ⟨x,sa x hx,y,tb y hy,dist⟩

/- Q3 has no triangle. Natural words here retain original coordinate bits
0,1,4, so the eight addresses do not run consecutively from 0 to 7. -/
def sites : List Nat := [0,1,2,3,16,17,18,19]
theorem edge_has_no_other_common_neighbour :
    sites.all (fun x => decide (Entry87.hamming x 2 > 1 ∨ Entry87.hamming x 3 > 1 ∨ x=2 ∨ x=3)) = true := by
  decide

#print axioms allTouch
#print axioms touching_subsets
#print axioms edge_has_no_other_common_neighbour
end Entry87.Shapes
