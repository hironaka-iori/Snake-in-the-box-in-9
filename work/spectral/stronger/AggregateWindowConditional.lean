import WindowPotential241
import UpperBound245

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate
noncomputable section
set_option maxHeartbeats 1600000

theorem psum_eq_sum (g : Nat → Nat) (n : Nat) : psum g n = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => rfl
  | succ n ih => simp [psum, ih, Finset.sum_range_succ]

/-- The count sequence of a snake, padded by zero. -/
def countSeq {m : Nat} (p : Snake m) (k : Nat) : Nat :=
  if hk : k<m+1 then localAlpha p ⟨k,hk⟩ else 0

theorem countSeq_eq {m : Nat} (p : Snake m) (k : Nat) (hk : k<m+1) :
    countSeq p k=localAlpha p ⟨k,hk⟩ := by simp [countSeq,hk]

/-- Endpoint, positivity, count-one-neighbour, and incidence facts, all proved. -/
theorem countSeq_facts {m : Nat} (p : Snake m) (hm3 : 3≤m) :
    4≤countSeq p 0 ∧ 4≤countSeq p m ∧
    (∀j,j<m-1 → 1≤countSeq p (j+1)) ∧
    (∀j,j+1<m-1 → PairOK (countSeq p (j+1)) (countSeq p (j+1+1))) ∧
    countSeq p 0+psum (fun j => countSeq p (j+1)) (m-1)+countSeq p m+35*(m+1)≤9214 := by
  have hm : 1≤m := by omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [countSeq_eq p 0 (by omega)]
    exact endpoint_alpha_ge_four p _ hm (Or.inl rfl)
  · rw [countSeq_eq p m (by omega)]
    exact endpoint_alpha_ge_four p _ hm (Or.inr rfl)
  · intro j hj
    rw [countSeq_eq p (j+1) (by omega)]
    exact localAlpha_positive p _
  · intro j hj
    rw [countSeq_eq p (j+1) (by omega),countSeq_eq p (j+1+1) (by omega)]
    have hadj : Adj (p.vertex ⟨j+1,by omega⟩) (p.vertex ⟨j+1+1,by omega⟩) :=
      (path_adj_iff p _ _).mpr (Or.inl rfl)
    exact ⟨alpha_one_neighbor_ge_four p hm _ _ hadj,
      alpha_one_neighbor_ge_four p hm _ _ (adj_symmetric hadj)⟩
  · have hsum : (∑j∈Finset.range (m+1),countSeq p j)=totalSingleton p := by
      rw [totalSingleton_eq_path_sum]
      exact (Finset.sum_fin_eq_sum_range (localAlpha p)).symm
    have hsplit : (∑j∈Finset.range (m+1),countSeq p j)=
        countSeq p 0+psum (fun j => countSeq p (j+1)) (m-1)+countSeq p m := by
      rw [psum_eq_sum,Finset.sum_range_succ]
      have he : m=(m-1)+1 := by omega
      conv_lhs => rw [he,Finset.sum_range_succ']
      omega
    have hidentity := global_identity p
    rw [selected_total p] at hidentity
    have hw := wedge_total_upper p
    rw [← hsum,hsplit] at hidentity
    omega

/-- Internal triples avoid `Excluded`, given the certified-window premise. -/
theorem countSeq_triples {m : Nat} (p : Snake m)
    (hcert : ∀r : Nat,∀hr : r+4≤m,
      ¬Certified (localAlpha p ⟨r+1,by omega⟩) (localAlpha p ⟨r+2,by omega⟩)
        (localAlpha p ⟨r+3,by omega⟩))
    (j : Nat) (hj : j+2<m-1) :
    ¬Excluded (countSeq p (j+1)) (countSeq p (j+1+1)) (countSeq p (j+2+1)) := by
  rw [countSeq_eq p (j+1) (by omega),countSeq_eq p (j+1+1) (by omega),
    countSeq_eq p (j+2+1) (by omega)]
  intro hE
  by_cases h222 : localAlpha p ⟨j+1,by omega⟩=2 ∧ localAlpha p ⟨j+1+1,by omega⟩=2 ∧
      localAlpha p ⟨j+2+1,by omega⟩=2
  · exact no_three_consecutive_internal_twos p j (by omega) h222
  · exact hcert j (by omega) ⟨hE,h222⟩

/-- Conditional 242-edge bound. The premise `hcert` excludes the internal windows
(2,2,3), (2,2,4), (2,3,2), (3,2,3), (4,1,c) with 4 ≤ c ≤ 6, and their reversals.
These have DRAT-checked certificates for the radius-three local ball model in
`milestones/10-window-aggregate/`, but the premise is NOT proved in Lean, so the
unconditional bound remains 245. -/
theorem upper_242_of_certified_windows {m : Nat} (p : Snake m)
    (hcert : ∀r : Nat,∀hr : r+4≤m,
      ¬Certified (localAlpha p ⟨r+1,by omega⟩) (localAlpha p ⟨r+2,by omega⟩)
        (localAlpha p ⟨r+3,by omega⟩)) : m≤242 := by
  by_cases hm3 : m<3
  · omega
  obtain ⟨h0,h1,hpos,hpair,hid⟩ := countSeq_facts p (by omega)
  have hcost := internal_cost (fun j => countSeq p (j+1)) (m-1) (by omega) hpos hpair
    (countSeq_triples p hcert)
  omega

/-- Conditional 241-edge bound: the premises of the 242 bound together with the
exclusion of internal windows (2,4,2,3) and (3,2,4,2), which are also DRAT-certified
for the local model but NOT proved in Lean. -/
theorem upper_241_of_certified_windows {m : Nat} (p : Snake m)
    (hcert : ∀r : Nat,∀hr : r+4≤m,
      ¬Certified (localAlpha p ⟨r+1,by omega⟩) (localAlpha p ⟨r+2,by omega⟩)
        (localAlpha p ⟨r+3,by omega⟩))
    (hquad : ∀r : Nat,∀hr : r+5≤m,
      ¬QuadExcluded (localAlpha p ⟨r+1,by omega⟩) (localAlpha p ⟨r+2,by omega⟩)
        (localAlpha p ⟨r+3,by omega⟩) (localAlpha p ⟨r+4,by omega⟩)) : m≤241 := by
  by_cases hm4 : m<4
  · omega
  obtain ⟨h0,h1,hpos,hpair,hid⟩ := countSeq_facts p (by omega)
  have hq (j : Nat) (hj : j+3<m-1) : ¬QuadExcluded (countSeq p (j+1)) (countSeq p (j+1+1))
      (countSeq p (j+2+1)) (countSeq p (j+3+1)) := by
    rw [countSeq_eq p (j+1) (by omega),countSeq_eq p (j+1+1) (by omega),
      countSeq_eq p (j+2+1) (by omega),countSeq_eq p (j+3+1) (by omega)]
    exact hquad j (by omega)
  have hcost := internal_cost3 (fun j => countSeq p (j+1)) (m-1) (by omega) hpos hpair
    (countSeq_triples p hcert) hq
  omega

#print axioms upper_242_of_certified_windows
#print axioms upper_241_of_certified_windows
end
end Snake9
