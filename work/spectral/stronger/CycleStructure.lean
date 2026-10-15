import PathStructure

/- A closed walk without an immediate backtrack cannot lie in a path.
   These finite six/eight-vertex forms do not require all pairs to be distinct. -/
namespace Snake9
set_option maxHeartbeats 1000000

theorem selected_cycle8_false {m : Nat} (p : Snake m)
    (v0 v1 v2 v3 v4 v5 v6 v7 : Vertex)
    (s0 : InPath p v0) (s1 : InPath p v1) (s2 : InPath p v2) (s3 : InPath p v3)
    (s4 : InPath p v4) (s5 : InPath p v5) (s6 : InPath p v6) (s7 : InPath p v7)
    (a01 : Adj v0 v1) (a12 : Adj v1 v2) (a23 : Adj v2 v3) (a34 : Adj v3 v4)
    (a45 : Adj v4 v5) (a56 : Adj v5 v6) (a67 : Adj v6 v7) (a70 : Adj v7 v0)
    (h71 : v7 ≠ v1) (h02 : v0 ≠ v2) (h13 : v1 ≠ v3) (h24 : v2 ≠ v4)
    (h35 : v3 ≠ v5) (h46 : v4 ≠ v6) (h57 : v5 ≠ v7) (h60 : v6 ≠ v0) : False := by
  obtain ⟨i0, rfl⟩ := s0
  obtain ⟨i1, rfl⟩ := s1
  obtain ⟨i2, rfl⟩ := s2
  obtain ⟨i3, rfl⟩ := s3
  obtain ⟨i4, rfl⟩ := s4
  obtain ⟨i5, rfl⟩ := s5
  obtain ⟨i6, rfl⟩ := s6
  obtain ⟨i7, rfl⟩ := s7
  have b01 := (path_adj_iff p i0 i1).mp a01
  have b12 := (path_adj_iff p i1 i2).mp a12
  have b23 := (path_adj_iff p i2 i3).mp a23
  have b34 := (path_adj_iff p i3 i4).mp a34
  have b45 := (path_adj_iff p i4 i5).mp a45
  have b56 := (path_adj_iff p i5 i6).mp a56
  have b67 := (path_adj_iff p i6 i7).mp a67
  have b70 := (path_adj_iff p i7 i0).mp a70
  have n71 : i7.val ≠ i1.val := fun h => h71 (congrArg p.vertex (Fin.ext h))
  have n02 : i0.val ≠ i2.val := fun h => h02 (congrArg p.vertex (Fin.ext h))
  have n13 : i1.val ≠ i3.val := fun h => h13 (congrArg p.vertex (Fin.ext h))
  have n24 : i2.val ≠ i4.val := fun h => h24 (congrArg p.vertex (Fin.ext h))
  have n35 : i3.val ≠ i5.val := fun h => h35 (congrArg p.vertex (Fin.ext h))
  have n46 : i4.val ≠ i6.val := fun h => h46 (congrArg p.vertex (Fin.ext h))
  have n57 : i5.val ≠ i7.val := fun h => h57 (congrArg p.vertex (Fin.ext h))
  have n60 : i6.val ≠ i0.val := fun h => h60 (congrArg p.vertex (Fin.ext h))
  omega

theorem selected_cycle6_false {m : Nat} (p : Snake m)
    (v0 v1 v2 v3 v4 v5 : Vertex)
    (s0 : InPath p v0) (s1 : InPath p v1) (s2 : InPath p v2)
    (s3 : InPath p v3) (s4 : InPath p v4) (s5 : InPath p v5)
    (a01 : Adj v0 v1) (a12 : Adj v1 v2) (a23 : Adj v2 v3)
    (a34 : Adj v3 v4) (a45 : Adj v4 v5) (a50 : Adj v5 v0)
    (h51 : v5 ≠ v1) (h02 : v0 ≠ v2) (h13 : v1 ≠ v3)
    (h24 : v2 ≠ v4) (h35 : v3 ≠ v5) (h40 : v4 ≠ v0) : False := by
  obtain ⟨i0, rfl⟩ := s0
  obtain ⟨i1, rfl⟩ := s1
  obtain ⟨i2, rfl⟩ := s2
  obtain ⟨i3, rfl⟩ := s3
  obtain ⟨i4, rfl⟩ := s4
  obtain ⟨i5, rfl⟩ := s5
  have b01 := (path_adj_iff p i0 i1).mp a01
  have b12 := (path_adj_iff p i1 i2).mp a12
  have b23 := (path_adj_iff p i2 i3).mp a23
  have b34 := (path_adj_iff p i3 i4).mp a34
  have b45 := (path_adj_iff p i4 i5).mp a45
  have b50 := (path_adj_iff p i5 i0).mp a50
  have n51 : i5.val ≠ i1.val := fun h => h51 (congrArg p.vertex (Fin.ext h))
  have n02 : i0.val ≠ i2.val := fun h => h02 (congrArg p.vertex (Fin.ext h))
  have n13 : i1.val ≠ i3.val := fun h => h13 (congrArg p.vertex (Fin.ext h))
  have n24 : i2.val ≠ i4.val := fun h => h24 (congrArg p.vertex (Fin.ext h))
  have n35 : i3.val ≠ i5.val := fun h => h35 (congrArg p.vertex (Fin.ext h))
  have n40 : i4.val ≠ i0.val := fun h => h40 (congrArg p.vertex (Fin.ext h))
  omega

#print axioms selected_cycle8_false
#print axioms selected_cycle6_false
end Snake9
