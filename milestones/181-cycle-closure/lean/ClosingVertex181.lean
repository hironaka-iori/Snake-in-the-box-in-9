import PathStructure
namespace Snake9.ClosingVertex181

theorem common_neighbor_absent {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (q : Vertex) (hgap : i.val+2<j.val)
    (hi : Adj (p.vertex i) q) (hj : Adj (p.vertex j) q) :
    ¬ InPath p q := by
  rintro ⟨k,hk⟩
  rw [←hk] at hi hj
  have h1 := (path_adj_iff p i k).mp hi
  have h2 := (path_adj_iff p j k).mp hj
  omega

theorem canonical_closing_neighbors :
    Adj (0 : Vertex) 4 ∧ Adj (12 : Vertex) 4 ∧
    Adj (0 : Vertex) 8 ∧ Adj (12 : Vertex) 8 := by decide

theorem canonical_window_excludes_closers {m : Nat} (p : Snake m)
    (i j : Fin (m+1)) (hgap : i.val+2<j.val)
    (hi : p.vertex i=0) (hj : p.vertex j=12) :
    ¬ InPath p (4 : Vertex) ∧ ¬ InPath p (8 : Vertex) := by
  have h := canonical_closing_neighbors
  constructor
  · exact common_neighbor_absent p i j 4 hgap (by rw [hi]; exact h.1)
      (by rw [hj]; exact h.2.1)
  · exact common_neighbor_absent p i j 8 hgap (by rw [hi]; exact h.2.2.1)
      (by rw [hj]; exact h.2.2.2)

#print axioms common_neighbor_absent
#print axioms canonical_closing_neighbors
#print axioms canonical_window_excludes_closers
end Snake9.ClosingVertex181
