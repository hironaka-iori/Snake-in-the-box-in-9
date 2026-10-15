import TwoMissingPairs
import NormalizeAdjacentSingletons

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1200000

structure EndpointMissingConfig {m : Nat} (p : Snake m) (a : Coord) where
  hzero : InPath p 0
  ha : InPath p (unit a)
  zero_low : AtMostOneNeighbor p 0
  cover : ∀ k : Coord, InPath p (unit k) → k=a
  F : Finset (Finset Coord)
  Fcard : F.card ≤ 3
  edge_card : ∀ s∈F, s.card=2
  avoids : ∀ s∈F, ∀ k∈s, k≠a
  selected_iff : ∀ i j : Coord, i≠j → i≠a → j≠a →
    (InPath p (pair i j) ↔ ({i,j} : Finset Coord)∉F)

theorem endpoint_index_low_degree {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hi : i.val=0 ∨ i.val=m) : AtMostOneNeighbor p (p.vertex i) := by
  intro u v hu hv hadju hadjv
  obtain ⟨j,rfl⟩ := hu
  obtain ⟨k,rfl⟩ := hv
  have hj := (path_adj_iff p i j).mp hadju
  have hk := (path_adj_iff p i k).mp hadjv
  have hjb := j.isLt
  have hkb := k.isLt
  have he : j.val=k.val := by omega
  exact congrArg p.vertex (Fin.ext he)

theorem endpoint_index_has_neighbor {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hm : 1≤m) (hi : i.val=0 ∨ i.val=m) : ∃ j, Adj (p.vertex i) (p.vertex j) := by
  rcases hi with hi | hi
  · refine ⟨⟨1,by omega⟩,(path_adj_iff p _ _).mpr (Or.inl ?_)⟩
    simpa only [hi]
  · refine ⟨⟨m-1,by omega⟩,(path_adj_iff p _ _).mpr (Or.inr ?_)⟩
    dsimp
    omega

theorem endpointMissingConfig_of_small_alpha {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hm : 1≤m) (hi : i.val=0 ∨ i.val=m) (halpha : localAlpha p i ≤ 3) :
    ∃ a : Coord, Nonempty (EndpointMissingConfig (translate p (p.vertex i)) a) := by
  let q := translate p (p.vertex i)
  have hqi : q.vertex i=0 := vxor_self _
  have hzero : InPath q 0 := ⟨i,hqi⟩
  have hlow : AtMostOneNeighbor q 0 := by rw [←hqi]; exact endpoint_index_low_degree q i hi
  obtain ⟨j,hj⟩ := endpoint_index_has_neighbor q i hm hi
  obtain ⟨a,ha⟩ := (adj_zero_iff (q.vertex j)).mp (hqi ▸ hj)
  have has : InPath q (unit a) := ⟨j,ha⟩
  have cover (k : Coord) (hk : InPath q (unit k)) : k=a := by
    exact unit_injective k a (hlow _ _ hk has
      ((adj_zero_iff _).mpr ⟨k,rfl⟩) ((adj_zero_iff _).mpr ⟨a,rfl⟩))
  have hcard : (missingPairSupports q).card ≤ 3 := by
    rw [missingPairSupports_card q i hqi,localAlpha_translate]
    exact halpha
  refine ⟨a,⟨⟨hzero,has,hlow,cover,missingPairSupports q,hcard,
    missingPairSupports_edge_card q,?_,?_⟩⟩⟩
  · exact fun s hs k hk => missingPairSupports_avoids_selected_unit q a has s hs k hk
  · intro r s hrs hra hsa
    have hr : ¬ InPath q (unit r) := fun h => hra (cover r h)
    have hs : ¬ InPath q (unit s) := fun h => hsa (cover s h)
    have he := mem_missingPairSupports_iff q hzero r s hrs
    simp only [hr,hs,not_false_eq_true,true_and] at he
    rw [he]
    exact not_not.symm

#print axioms endpointMissingConfig_of_small_alpha
end
end Snake9
