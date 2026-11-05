import Snake9

namespace Snake9
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem adj_symmetric {u v : Vertex} (h : Adj u v) : Adj v u := by
  obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip u v).mp h
  apply (adj_iff_coordinate_flip v u).mpr
  refine ⟨k,hk,?_⟩
  rw [he]
  change u.val = (u.val ^^^ 2^k) ^^^ 2^k
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem adj_irreflexive (u : Vertex) : ¬ Adj u u := by
  intro h
  obtain ⟨k, hk, he⟩ := (adj_iff_coordinate_flip u u).mp h
  have hh : 0 = 2^k := calc
    0 = u.val ^^^ u.val := (Nat.xor_self _).symm
    _ = u.val ^^^ (u.val ^^^ 2^k) := congrArg (fun z => u.val ^^^ z) he
    _ = (u.val ^^^ u.val) ^^^ 2^k := (Nat.xor_assoc _ _ _).symm
    _ = 2^k := by rw [Nat.xor_self, Nat.zero_xor]
  have hp : 0 < 2^k := Nat.two_pow_pos k
  omega

theorem path_adj_iff {m : Nat} (p : Snake m) (i j : Fin (m+1)) :
    Adj (p.vertex i) (p.vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  rcases Nat.lt_trichotomy i.val j.val with hlt | he | hgt
  · rw [p.induced i j hlt]
    omega
  · have hij : i=j := Fin.ext he
    subst j
    simp only [adj_irreflexive, false_iff]
    omega
  · have hs : Adj (p.vertex i) (p.vertex j) ↔ Adj (p.vertex j) (p.vertex i) :=
      ⟨adj_symmetric,adj_symmetric⟩
    rw [hs,p.induced j i hgt]
    omega

theorem three_neighbors_repeat {m : Nat} (p : Snake m)
    (i j k l : Fin (m+1))
    (hj : Adj (p.vertex i) (p.vertex j))
    (hk : Adj (p.vertex i) (p.vertex k))
    (hl : Adj (p.vertex i) (p.vertex l)) : j=k ∨ j=l ∨ k=l := by
  have hj' := (path_adj_iff p i j).mp hj
  have hk' := (path_adj_iff p i k).mp hk
  have hl' := (path_adj_iff p i l).mp hl
  have hv : j.val=k.val ∨ j.val=l.val ∨ k.val=l.val := by omega
  rcases hv with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

def InPath {m : Nat} (p : Snake m) (v : Vertex) : Prop := ∃ i, p.vertex i=v

theorem selected_three_neighbors_repeat {m : Nat} (p : Snake m)
    {v a b c : Vertex} (hv : InPath p v) (ha : InPath p a)
    (hb : InPath p b) (hc : InPath p c)
    (hva : Adj v a) (hvb : Adj v b) (hvc : Adj v c) :
    a=b ∨ a=c ∨ b=c := by
  obtain ⟨i,rfl⟩ := hv
  obtain ⟨j,rfl⟩ := ha
  obtain ⟨k,rfl⟩ := hb
  obtain ⟨l,rfl⟩ := hc
  rcases three_neighbors_repeat p i j k l hva hvb hvc with h | h | h
  · exact Or.inl (congrArg p.vertex h)
  · exact Or.inr (Or.inl (congrArg p.vertex h))
  · exact Or.inr (Or.inr (congrArg p.vertex h))

def AtMostOneNeighbor {m : Nat} (p : Snake m) (v : Vertex) : Prop :=
  ∀ a b, InPath p a → InPath p b → Adj v a → Adj v b → a=b

theorem low_degree_index_is_endpoint {m : Nat} (p : Snake m) (i : Fin (m+1))
    (h : AtMostOneNeighbor p (p.vertex i)) : i.val=0 ∨ i.val=m := by
  by_cases hnot : i.val=0 ∨ i.val=m
  · exact hnot
  have hi0 : 0 < i.val := by omega
  have him : i.val < m := by omega
  let left : Fin (m+1) := ⟨i.val-1,by omega⟩
  let right : Fin (m+1) := ⟨i.val+1,by omega⟩
  have hl : Adj (p.vertex i) (p.vertex left) :=
    (path_adj_iff p i left).mpr (Or.inr (by dsimp [left]; omega))
  have hr : Adj (p.vertex i) (p.vertex right) :=
    (path_adj_iff p i right).mpr (Or.inl rfl)
  have he := p.distinct left right (h _ _ ⟨left,rfl⟩ ⟨right,rfl⟩ hl hr)
  have hev := congrArg Fin.val he
  dsimp [left,right] at hev
  omega

theorem three_low_degree_vertices_repeat {m : Nat} (p : Snake m)
    {a b c : Vertex} (ha : InPath p a) (hb : InPath p b) (hc : InPath p c)
    (la : AtMostOneNeighbor p a) (lb : AtMostOneNeighbor p b)
    (lc : AtMostOneNeighbor p c) : a=b ∨ a=c ∨ b=c := by
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hb
  obtain ⟨k,rfl⟩ := hc
  have h1 := low_degree_index_is_endpoint p i la
  have h2 := low_degree_index_is_endpoint p j lb
  have h3 := low_degree_index_is_endpoint p k lc
  have he : i.val=j.val ∨ i.val=k.val ∨ j.val=k.val := by omega
  rcases he with h | h | h
  · exact Or.inl (congrArg p.vertex (Fin.ext h))
  · exact Or.inr (Or.inl (congrArg p.vertex (Fin.ext h)))
  · exact Or.inr (Or.inr (congrArg p.vertex (Fin.ext h)))

#print axioms selected_three_neighbors_repeat
#print axioms low_degree_index_is_endpoint
#print axioms three_low_degree_vertices_repeat
end Snake9
