import AlphaRunPotential
import UpperBound247
import AdjacentOneThreeExclusion

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1600000

theorem alpha_one_neighbor_ge_four {m : Nat} (p : Snake m) (hm : 1≤m)
    (i j : Fin (m+1)) (hadj : Adj (p.vertex i) (p.vertex j))
    (hi : localAlpha p i=1) : 4≤localAlpha p j := by
  have hin : ¬(i.val=0 ∨ i.val=m) := by
    intro he
    have hh := endpoint_alpha_ge_four p i hm he
    omega
  by_cases hj : j.val=0 ∨ j.val=m
  · exact endpoint_alpha_ge_four p j hm hj
  · exact alpha_one_internal_neighbor_ge_four p i j (by omega) (by omega)
      (by omega) (by omega) hadj hi

/-- This theorem does not discharge the no-three-twos premise. -/
theorem upper_245_of_no_three_twos {m : Nat} (p : Snake m)
    (hno : ∀r : Nat,∀hr : r+4≤m,
      ¬(localAlpha p ⟨r+1,by omega⟩=2 ∧ localAlpha p ⟨r+2,by omega⟩=2 ∧
        localAlpha p ⟨r+3,by omega⟩=2)) : m≤245 := by
  by_cases hm0 : m=0
  · omega
  have hm : 1≤m := by omega
  let f : Nat → Nat := fun k => if hk : k<m+1 then localAlpha p ⟨k,hk⟩ else 0
  have hf (k : Nat) (hk : k<m+1) : f k=localAlpha p ⟨k,hk⟩ := by simp [f,hk]
  have hfirst : 4≤f 0 := by
    rw [hf 0 (by omega)]
    exact endpoint_alpha_ge_four p _ hm (Or.inl rfl)
  have hlast : 4≤f m := by
    rw [hf m (by omega)]
    exact endpoint_alpha_ge_four p _ hm (Or.inr rfl)
  have hpos (j : Nat) (hj : j<m+1) : 1≤f j := by
    rw [hf j hj]
    exact localAlpha_positive p _
  have hone (j : Nat) (hj : j+1<m+1) :
      (f j=1 → 4≤f (j+1)) ∧ (f (j+1)=1 → 4≤f j) := by
    rw [hf j (by omega),hf (j+1) hj]
    have hadj : Adj (p.vertex ⟨j,by omega⟩) (p.vertex ⟨j+1,hj⟩) :=
      (path_adj_iff p _ _).mpr (Or.inl rfl)
    exact ⟨alpha_one_neighbor_ge_four p hm _ _ hadj,
      alpha_one_neighbor_ge_four p hm _ _ (adj_symmetric hadj)⟩
  have h222 (j : Nat) (hj : j+2<m+1) : ¬(f j=2 ∧ f (j+1)=2 ∧ f (j+2)=2) := by
    rintro ⟨h1,h2,h3⟩
    have hj0 : j≠0 := by intro he; subst j; omega
    have hjm : j+2≠m := by intro he; rw [he] at h3; omega
    have he1 : j-1+1=j := by omega
    have he2 : j-1+2=j+1 := by omega
    have he3 : j-1+3=j+2 := by omega
    apply hno (j-1) (by omega)
    simpa only [he1,he2,he3] using And.intro ((hf j (by omega)).symm.trans h1)
      (And.intro ((hf (j+1) (by omega)).symm.trans h2) ((hf (j+2) hj).symm.trans h3))
  have hcost := alpha_sequence_cost f (m+1) (by omega) hfirst (by simpa using hlast) hpos hone h222
  have hsum : (∑j∈Finset.range (m+1),f j)=totalSingleton p := by
    rw [totalSingleton_eq_path_sum]
    exact (Finset.sum_fin_eq_sum_range (localAlpha p)).symm
  rw [hsum] at hcost
  have hidentity := global_identity p
  rw [selected_total p] at hidentity
  have hw := wedge_total_upper p
  omega

#print axioms upper_245_of_no_three_twos
end
end Snake9
