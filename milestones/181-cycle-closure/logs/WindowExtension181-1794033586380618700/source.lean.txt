import PathStructure
namespace Snake9.WindowExtension181
theorem window_must_extend {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (hij : i.val+6=j.val) (hm : 7≤m) :
    ∃ k : Fin (m+1), (k.val<i.val ∨ j.val<k.val) ∧
      (Adj (p.vertex i) (p.vertex k) ∨ Adj (p.vertex j) (p.vertex k)) := by
  by_cases hi : 0<i.val
  · let k : Fin (m+1) := ⟨i.val-1,by omega⟩
    refine ⟨k,Or.inl (by dsimp [k]; omega),Or.inl ?_⟩
    apply (path_adj_iff p i k).mpr
    right
    dsimp [k]
    omega
  · have hj : j.val<m := by omega
    let k : Fin (m+1) := ⟨j.val+1,by omega⟩
    refine ⟨k,Or.inr (by dsimp [k]; omega),Or.inr ?_⟩
    apply (path_adj_iff p j k).mpr
    left
    rfl
#print axioms window_must_extend
end Snake9.WindowExtension181
