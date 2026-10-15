import AggregateSingletonBound
import SingletonGeometry

namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem vxor_zero_left (v : Vertex) : vxor 0 v = v := by
  apply Fin.ext
  exact Nat.zero_xor _

theorem vxor_assoc' (a b c : Vertex) : vxor a (vxor b c) = vxor (vxor a b) c := by
  apply Fin.ext
  exact (Nat.xor_assoc _ _ _).symm

theorem inPath_translate_iff {m : Nat} (p : Snake m) (t v : Vertex) :
    InPath (translate p t) (vxor t v) ↔ InPath p v := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, vxor_injective t hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

theorem translate_flip (t v : Vertex) (a : Coord) :
    flip a (vxor t v) = vxor t (flip a v) := (vxor_assoc' t v (unit a)).symm

theorem singleton_translate {m : Nat} (p : Snake m) (t v : Vertex) (ab : AxisPair) :
    singleton (translate p t) ab (vxor t v) = singleton p ab v := by
  unfold singleton
  simp only [translate_flip, inPath_translate_iff]

theorem localAlpha_translate {m : Nat} (p : Snake m) (t : Vertex) (i : Fin (m+1)) :
    localAlpha (translate p t) i = localAlpha p i := by
  unfold localAlpha
  apply Finset.sum_congr rfl
  intro ab _
  exact singleton_translate p t (p.vertex i) ab

theorem singleton_one_unique {m : Nat} (p : Snake m) (i : Fin (m+1))
    (h : localAlpha p i = 1) (ab cd : AxisPair)
    (hab : singleton p ab (p.vertex i) = 1)
    (hcd : singleton p cd (p.vertex i) = 1) : ab = cd := by
  by_contra hn
  have hle : (∑ q ∈ ({ab, cd} : Finset AxisPair), singleton p q (p.vertex i)) ≤
      ∑ q : AxisPair, singleton p q (p.vertex i) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have he : (∑ q ∈ ({ab, cd} : Finset AxisPair), singleton p q (p.vertex i)) = 2 := by
    simp [hn,hab,hcd]
  change _ ≤ localAlpha p i at hle
  omega

theorem singleton_at_zero_iff {m : Nat} (p : Snake m) (ab : AxisPair) :
    singleton p ab 0 = 1 ↔ InPath p 0 ∧ ¬ InPath p (unit ab.val.1) ∧
      ¬ InPath p (unit ab.val.2) ∧ ¬ InPath p (pair ab.val.1 ab.val.2) := by
  simp [singleton, flip, vxor_zero_left, pair]

theorem alpha_one_forced_pairs_zero {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hz : p.vertex i = 0) (ha : localAlpha p i = 1) :
    ∃ c d : Coord, c ≠ d ∧ ¬ InPath p (unit c) ∧ ¬ InPath p (unit d) ∧
      ¬ InPath p (pair c d) ∧ ForcedPairsExcept p c d := by
  obtain ⟨a,b,h⟩ := singleton_square_exists p i
  let ab : AxisPair := ⟨(⟨a,h.1⟩,⟨b,h.2.1⟩),h.2.2.1⟩
  have hab : singleton p ab (p.vertex i) = 1 := by
    apply if_pos
    refine ⟨⟨i,rfl⟩,?_,?_,?_⟩
    · rintro ⟨j,hj⟩
      exact (h.2.2.2 j).1 (congrArg Fin.val hj)
    · rintro ⟨j,hj⟩
      exact (h.2.2.2 j).2.1 (congrArg Fin.val hj)
    · rintro ⟨j,hj⟩
      exact (h.2.2.2 j).2.2 (congrArg Fin.val hj)
  have hzab : singleton p ab 0 = 1 := hz ▸ hab
  have hcond := (singleton_at_zero_iff p ab).mp hzab
  refine ⟨ab.val.1,ab.val.2,?_,hcond.2.1,hcond.2.2.1,hcond.2.2.2,?_⟩
  · exact fun he => (ne_of_lt ab.property) (congrArg Fin.val he)
  intro c d hcd hc hd hnot
  by_contra hpair
  by_cases hlt : c.val < d.val
  · let cd : AxisPair := ⟨(c,d),hlt⟩
    have hcd1 : singleton p cd (p.vertex i) = 1 := by
      rw [hz]
      exact (singleton_at_zero_iff p cd).mpr ⟨hcond.1,hc,hd,hpair⟩
    have he := singleton_one_unique p i ha cd ab hcd1 hab
    have hv := congrArg Subtype.val he
    exact hnot (Or.inl ⟨congrArg Prod.fst hv,congrArg Prod.snd hv⟩)
  · have hlt' : d.val < c.val := by
      have hne : c.val ≠ d.val := fun he => hcd (Fin.ext he)
      omega
    let dc : AxisPair := ⟨(d,c),hlt'⟩
    have hdc1 : singleton p dc (p.vertex i) = 1 := by
      rw [hz]
      apply (singleton_at_zero_iff p dc).mpr
      refine ⟨hcond.1,hd,hc,?_⟩
      change ¬ InPath p (pair d c)
      rw [pair_comm d c]
      exact hpair
    have he := singleton_one_unique p i ha dc ab hdc1 hab
    have hv := congrArg Subtype.val he
    exact hnot (Or.inr ⟨congrArg Prod.snd hv,congrArg Prod.fst hv⟩)

#print axioms localAlpha_translate
#print axioms alpha_one_forced_pairs_zero
end
end Snake9.SquareIncidence
