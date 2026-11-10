import AggregateWindowUnconditional
import ShareCharge
import LocalWindowShareBridge

/-!
# The corner share of a snake vertex: global (mathlib) = core

Glue for the s0 route (`milestones/11-local-ceiling/s0_lean_design.md`, §1 "Path-indexed
form" and the identification announced in `work/final_lean/LocalWindowShareBridge.lean`).

* `emptyAt_eq_emptyCount` : `emptyAt p q = emptyCount (sel p id) q.val` (bijection
  `AxisPair ↔ freePairs 9 9`, as `localAlpha_eq_coreAlpha`);
* `selDeg_eq_cnt`         : `selDeg p q = cnt (sel p id) (nbrs q.val)` (`cnt_nbrs_eq`);
* `shareN_eq_coreShare`   : `shareN M p (p.vertex k) = coreShare M p k`;
* `shareSeq`, `charge_sum_le`, `charge_facts`, `core_charge_sum_le` : the path-indexed
  form of `charge_total_le`,
  `Σ_{k ≤ m} (2M·α_k + share_k) + 70 M (m+1) ≤ 18428 M`, in the `countSeq`/`psum` shape of
  `countSeq_facts` and in the core `coreAlpha`/`coreShare` shape the automaton consumes.
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate LocalWindow
noncomputable section
set_option maxHeartbeats 1600000

/-! ## Sums over `Fin n`, `Finset.range n` and `List.range n` -/

theorem sum_range_eq_list_sum (f : Nat → Nat) (n : Nat) :
    (∑ k ∈ Finset.range n, f k) = ((List.range n).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

theorem sum_fin_eq_list_sum (f : Nat → Nat) (n : Nat) :
    (∑ k : Fin n, f k.val) = ((List.range n).map f).sum := by
  rw [← Finset.sum_range, sum_range_eq_list_sum]

/-- `Σ_x sel(x)·f(x) = Σ_i f(p.vertex i)` (as `selected_total`, `totalSingleton_eq_path_sum`). -/
theorem sum_selected_mul {m : Nat} (p : Snake m) (f : Vertex → Nat) :
    (∑ x, selected p x * f x) = ∑ i : Fin (m + 1), f (p.vertex i) := by
  let s : Finset Vertex := Finset.univ.image p.vertex
  have hs : ∀ v, selected p v * f v = if v ∈ s then f v else 0 := by
    intro v
    have hv : InPath p v ↔ v ∈ s := by simp [s, InPath]
    unfold selected
    rw [hv]
    split <;> simp
  simp only [hs]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image]
  intro i _ j _ h
  exact p.distinct i j h

/-! ## Empty squares and selected neighbours -/

/-- `emptyAt` is the core `emptyCount` in the identity frame. -/
theorem emptyAt_eq_emptyCount {m : Nat} (p : Snake m) (q : Vertex) :
    emptyAt p q = emptyCount (sel p (fun w => w)) q.val := by
  have hterm : ∀ ab : AxisPair, empty p ab q =
      if emptyPred (sel p (fun w => w)) q.val (ab.val.1.val, ab.val.2.val) = true
      then 1 else 0 := by
    intro ab
    unfold empty
    simp only [inPath_iff_sel, flip_val]
    cases h0 : sel p (fun w => w) q.val <;>
    cases h1 : sel p (fun w => w) (q.val ^^^ 2 ^ ab.val.1.val) <;>
    cases h2 : sel p (fun w => w) (q.val ^^^ 2 ^ ab.val.2.val) <;>
    cases h3 : sel p (fun w => w) (q.val ^^^ 2 ^ ab.val.1.val ^^^ 2 ^ ab.val.2.val) <;>
    simp [emptyPred_iff, h0, h1, h2, h3]
  unfold emptyAt emptyCount
  rw [Finset.sum_congr rfl (fun ab _ => hterm ab), Finset.sum_boole, Nat.cast_id,
    ← List.toFinset_card_of_nodup ((freePairs_nodup 9 (by omega) 9 (by omega)).filter _)]
  apply Finset.card_bij (fun ab _ => (ab.val.1.val, ab.val.2.val))
  · intro ab hab
    rw [Finset.mem_filter] at hab
    rw [List.mem_toFinset, List.mem_filter, mem_freePairs]
    exact ⟨⟨ab.2, ab.val.2.isLt, by omega, by omega, by omega, by omega⟩, hab.2⟩
  · intro a₁ _ a₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Subtype.ext (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  · intro b hb
    obtain ⟨u, w⟩ := b
    rw [List.mem_toFinset, List.mem_filter, mem_freePairs] at hb
    obtain ⟨⟨h1, h2, -⟩, h3⟩ := hb
    refine ⟨⟨(⟨u, by omega⟩, ⟨w, h2⟩), h1⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h3⟩

/-- `selDeg` is the core selected-neighbour count `cnt S (nbrs ·)`. -/
theorem selDeg_eq_cnt {m : Nat} (p : Snake m) (q : Vertex) :
    selDeg p q = cnt (sel p (fun w => w)) (nbrs q.val) := by
  rw [cnt_nbrs_eq]
  unfold selDeg selected
  simp only [inPath_iff_sel, flip_val]
  rw [Finset.sum_boole, Nat.cast_id, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨k.isLt, hk.2⟩
  · intro a _ b _ h
    exact Fin.ext h
  · intro b hb
    rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩, rfl⟩

/-! ## The share identification -/

/-- The global share `shareN` of the snake's `k`-th vertex is the core `coreShare`. -/
theorem shareN_eq_coreShare {m : Nat} (M : Nat) (p : Snake m) (k : Nat) (hk : k < m + 1) :
    shareN M p (p.vertex ⟨k, hk⟩) = coreShare M p k := by
  have hc : vx p k = (p.vertex ⟨k, hk⟩).val := by simp [vx, hk]
  rw [coreShare_eq_sum, hc]
  unfold shareN
  simp only [emptyAt_eq_emptyCount, selDeg_eq_cnt, flip_val]
  exact sum_fin_eq_list_sum (fun j => M * emptyCount (sel p fun w => w)
    ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ j) / cnt (sel p fun w => w)
    (nbrs ((p.vertex ⟨k, hk⟩).val ^^^ 2 ^ j))) 9

/-! ## Path-indexed form -/

/-- The share sequence of a snake, padded by zero (as `countSeq`). -/
def shareSeq {m : Nat} (M : Nat) (p : Snake m) (k : Nat) : Nat :=
  if hk : k < m + 1 then shareN M p (p.vertex ⟨k, hk⟩) else 0

theorem shareSeq_eq {m : Nat} (M : Nat) (p : Snake m) (k : Nat) (hk : k < m + 1) :
    shareSeq M p k = shareN M p (p.vertex ⟨k, hk⟩) := by simp [shareSeq, hk]

theorem shareSeq_eq_coreShare {m : Nat} (M : Nat) (p : Snake m) (k : Nat) (hk : k ≤ m) :
    shareSeq M p k = coreShare M p k := by
  rw [shareSeq_eq M p k (by omega), shareN_eq_coreShare]

theorem countSeq_eq_coreAlpha_le {m : Nat} (p : Snake m) (k : Nat) (hk : k ≤ m) :
    countSeq p k = coreAlpha p k := by
  rw [countSeq_eq p k (by omega), localAlpha_eq_coreAlpha]

/-- The weighted incidence inequality over the path indices. -/
theorem charge_sum_le {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.range (m + 1), (2 * M * countSeq p j + shareSeq M p j)) + 70 * M * (m + 1)
      ≤ 18428 * M := by
  have h := charge_total_le M p hm
  rw [sum_selected_mul p (fun x => 2 * M * (∑ ab : AxisPair, singleton p ab x) + shareN M p x),
    Finset.sum_fin_eq_sum_range] at h
  have hsum : (∑ j ∈ Finset.range (m + 1), (2 * M * countSeq p j + shareSeq M p j)) =
      ∑ j ∈ Finset.range (m + 1), if hj : j < m + 1 then
        2 * M * (∑ ab : AxisPair, singleton p ab (p.vertex ⟨j, hj⟩)) +
          shareN M p (p.vertex ⟨j, hj⟩) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [dif_pos hj, countSeq_eq p j hj, shareSeq_eq M p j hj]
    rfl
  rw [hsum]
  exact h

theorem sum_range_split (g : Nat → Nat) (m : Nat) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.range (m + 1), g j) = g 0 + psum (fun j => g (j + 1)) (m - 1) + g m := by
  rw [psum_eq_sum, Finset.sum_range_succ]
  have he : Finset.range m = Finset.range ((m - 1) + 1) := by congr 1; omega
  rw [he, Finset.sum_range_succ']
  omega

/-- The path-indexed charge inequality in the `countSeq`/`psum` shape of `countSeq_facts`
(design §1): `2M (Σ α) + Σ share + 70 M (m+1) ≤ 18428 M`. -/
theorem charge_facts {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    2 * M * (countSeq p 0 + psum (fun j => countSeq p (j + 1)) (m - 1) + countSeq p m)
      + (shareSeq M p 0 + psum (fun j => shareSeq M p (j + 1)) (m - 1) + shareSeq M p m)
      + 70 * M * (m + 1) ≤ 18428 * M := by
  have h := charge_sum_le M p hm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_split (countSeq p) m hm,
    sum_range_split (shareSeq M p) m hm] at h
  exact h

/-- The path-indexed charge inequality in core terms:
`Σ_{k ≤ m} (2M·coreAlpha p k + coreShare M p k) + 70 M (m+1) ≤ 18428 M`. -/
theorem core_charge_sum_le {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.range (m + 1), (2 * M * coreAlpha p k + coreShare M p k)) + 70 * M * (m + 1)
      ≤ 18428 * M := by
  have h := charge_sum_le M p hm
  have e : (∑ k ∈ Finset.range (m + 1), (2 * M * coreAlpha p k + coreShare M p k)) =
      ∑ k ∈ Finset.range (m + 1), (2 * M * countSeq p k + shareSeq M p k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [countSeq_eq_coreAlpha_le p k (by omega), shareSeq_eq_coreShare M p k (by omega)]
  rw [e]
  exact h

/-- Core form with the interior shares isolated (the shape of `refuted_share_bridge`'s
conclusion `K + 1 ≤ Σ_i coreShare M p (r + i + 1)` summed over disjoint windows):
`Σ_{k ≤ m} 2M·coreAlpha p k + coreShare M p 0 + Σ_{j < m-1} coreShare M p (j+1)
  + coreShare M p m + 70 M (m+1) ≤ 18428 M`. -/
theorem core_charge_facts {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    2 * M * (∑ k ∈ Finset.range (m + 1), coreAlpha p k)
      + (coreShare M p 0 + ((List.range (m - 1)).map fun j => coreShare M p (j + 1)).sum
          + coreShare M p m)
      + 70 * M * (m + 1) ≤ 18428 * M := by
  have h := core_charge_sum_le M p hm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_split (coreShare M p) m hm,
    psum_eq_sum, sum_range_eq_list_sum] at h
  exact h

#print axioms shareN_eq_coreShare
#print axioms charge_sum_le
#print axioms charge_facts
#print axioms core_charge_sum_le
#print axioms core_charge_facts
end
end Snake9
