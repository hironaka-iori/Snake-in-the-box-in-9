import AdjacentConfiguration

namespace Snake9.SquareIncidence
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 1000000

def axisPairSupport (ab : AxisPair) : Finset Coord := {ab.val.1, ab.val.2}

theorem axisPairSupport_card (ab : AxisPair) : (axisPairSupport ab).card = 2 := by
  have hn : ab.val.1 ≠ ab.val.2 := fun h => (ne_of_lt ab.property) (congrArg Fin.val h)
  simp [axisPairSupport, hn]

theorem pair_support_eq_iff (i j k l : Coord) (hij : i ≠ j) (hkl : k ≠ l) :
    ({i,j} : Finset Coord) = {k,l} ↔ (i=k ∧ j=l) ∨ (i=l ∧ j=k) := by
  constructor
  · intro h
    have hi : i=k ∨ i=l := by have := h ▸ (show i ∈ ({i,j} : Finset Coord) by simp); simpa using this
    have hj : j=k ∨ j=l := by have := h ▸ (show j ∈ ({i,j} : Finset Coord) by simp); simpa using this
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact False.elim (hij (hi.trans hj.symm))
    · exact Or.inl ⟨hi,hj⟩
    · exact Or.inr ⟨hi,hj⟩
    · exact False.elim (hij (hi.trans hj.symm))
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact Finset.pair_comm _ _

theorem axisPairSupport_injective : Function.Injective axisPairSupport := by
  intro ab cd he
  have hab : ab.val.1 ≠ ab.val.2 := fun h => (ne_of_lt ab.property) (congrArg Fin.val h)
  have hcd : cd.val.1 ≠ cd.val.2 := fun h => (ne_of_lt cd.property) (congrArg Fin.val h)
  rcases (pair_support_eq_iff _ _ _ _ hab hcd).mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · have h := ab.property
    rw [h1,h2] at h
    exact False.elim (Nat.lt_asymm h cd.property)

def missingAxisPairs {m : Nat} (p : Snake m) : Finset AxisPair :=
  Finset.univ.filter (fun ab => singleton p ab 0 = 1)

def missingPairSupports {m : Nat} (p : Snake m) : Finset (Finset Coord) :=
  (missingAxisPairs p).image axisPairSupport

theorem missingAxisPairs_card {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hz : p.vertex i = 0) : (missingAxisPairs p).card = localAlpha p i := by
  unfold missingAxisPairs localAlpha
  rw [hz, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ab _
  unfold singleton
  split_ifs <;> simp_all

theorem missingPairSupports_card {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hz : p.vertex i = 0) : (missingPairSupports p).card = localAlpha p i := by
  rw [missingPairSupports, Finset.card_image_of_injective _ axisPairSupport_injective]
  exact missingAxisPairs_card p i hz

theorem missingPairSupports_edge_card {m : Nat} (p : Snake m) (s : Finset Coord)
    (hs : s ∈ missingPairSupports p) : s.card = 2 := by
  obtain ⟨ab,_,rfl⟩ := Finset.mem_image.mp hs
  exact axisPairSupport_card ab

theorem mem_missingPairSupports_iff {m : Nat} (p : Snake m) (hz : InPath p 0)
    (i j : Coord) (hij : i ≠ j) :
    ({i,j} : Finset Coord) ∈ missingPairSupports p ↔
      ¬ InPath p (unit i) ∧ ¬ InPath p (unit j) ∧ ¬ InPath p (pair i j) := by
  constructor
  · intro hs
    obtain ⟨ab,hm,he⟩ := Finset.mem_image.mp hs
    have hm' : singleton p ab 0 = 1 := (Finset.mem_filter.mp hm).2
    have hp := (singleton_at_zero_iff p ab).mp hm'
    have hab : ab.val.1 ≠ ab.val.2 := fun h => (ne_of_lt ab.property) (congrArg Fin.val h)
    rcases (pair_support_eq_iff _ _ _ _ hab hij).mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · simpa only [h1,h2] using hp.2
    · rw [h1,h2] at hp
      exact ⟨hp.2.2.1,hp.2.1,by simpa only [pair_comm j i] using hp.2.2.2⟩
  · rintro ⟨hi,hj,hp⟩
    by_cases hlt : i.val < j.val
    · let ab : AxisPair := ⟨(i,j),hlt⟩
      apply Finset.mem_image.mpr
      refine ⟨ab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact (singleton_at_zero_iff p ab).mpr ⟨hz,hi,hj,hp⟩
    · have hlt' : j.val < i.val := by
        have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
        omega
      let ab : AxisPair := ⟨(j,i),hlt'⟩
      apply Finset.mem_image.mpr
      refine ⟨ab, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.pair_comm _ _⟩
      exact (singleton_at_zero_iff p ab).mpr ⟨hz,hj,hi,by change ¬ InPath p (pair j i); simpa only [pair_comm j i] using hp⟩

theorem missingPairSupports_avoids_selected_unit {m : Nat} (p : Snake m)
    (a : Coord) (ha : InPath p (unit a)) (s : Finset Coord)
    (hs : s ∈ missingPairSupports p) (k : Coord) (hk : k ∈ s) : k ≠ a := by
  obtain ⟨ab,hm,rfl⟩ := Finset.mem_image.mp hs
  have hp := (singleton_at_zero_iff p ab).mp (Finset.mem_filter.mp hm).2
  have hk' : k = ab.val.1 ∨ k = ab.val.2 := by simpa [axisPairSupport] using hk
  intro he
  rcases hk' with h | h
  · exact hp.2.1 (by simpa only [←h,he] using ha)
  · exact hp.2.2.1 (by simpa only [←h,he] using ha)

theorem missingPairSupports_two {m : Nat} (p : Snake m) (i : Fin (m+1))
    (hz : p.vertex i = 0) (ha : localAlpha p i = 2) :
    ∃ f g : Finset Coord, f ≠ g ∧ missingPairSupports p = {f,g} ∧ f.card = 2 ∧ g.card = 2 := by
  have hc : (missingPairSupports p).card = 2 := (missingPairSupports_card p i hz).trans ha
  obtain ⟨f,g,hfg,hF⟩ := Finset.card_eq_two.mp hc
  refine ⟨f,g,hfg,hF,?_,?_⟩
  · exact missingPairSupports_edge_card p f (by rw [hF]; simp)
  · exact missingPairSupports_edge_card p g (by rw [hF]; simp)

#print axioms missingPairSupports_card
#print axioms mem_missingPairSupports_iff
#print axioms missingPairSupports_two
end
end Snake9.SquareIncidence
