import ShareFrame
import ShareBound0
namespace Snake9.LocalWindow.ShareObstruction530
def directions : List Nat := [0, 1, 2, 0, 3, 4]
theorem share_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) :
    96 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  exact refuted_share_bridge p P r refuted_share
    (cs := directions) ⟨rfl,rfl,by decide⟩ (by decide) hr hd hb
theorem named_share_in_snake {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hb : ∀ i, i<5 → (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) :
    96 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply share_in_snake p (mkPerm [a,b,c,d,e]) r hr ?_ hb
  intro j hj
  rw [hd j hj]
  interval_cases j
  · exact hs 0 (by simp)
  · exact hs 1 (by simp)
  · exact hs 2 (by simp)
  · exact hs 0 (by simp)
  · exact hs 3 (by simp)
  · exact hs 4 (by simp)
#print axioms share_in_snake
#print axioms named_share_in_snake
end Snake9.LocalWindow.ShareObstruction530
