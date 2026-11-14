import SupportBridge212

/-!
Source prepared for checking; not compiled by its author.
The candidate-partner list N may overestimate the actual supported
partners. Domain fitting and geometric partner completeness are explicit
hypotheses; no native matching or search implementation is certified.
-/

namespace PartnerSubset212

/-- A subset of outside variables cannot exceed its supported partner
capacity plus the spare word capacity. N contains every listed chosen
partner whose domain intersects a subset member's domain. -/
theorem partner_subset_capacity
    (C O pool J N : List Nat)
    (values : Nat → Nat) (domains partners : Nat → List Nat)
    (hC : (C.map values).Nodup)
    (hO : (O.map values).Nodup)
    (hJ : (J.map values).Nodup)
    (hCpool : ∀ c, c ∈ C → values c ∈ pool)
    (hOpool : ∀ i, i ∈ O → values i ∈ pool)
    (hJO : ∀ i, i ∈ J → i ∈ O)
    (hfit : ∀ i, values i ∈ domains i)
    (hpartners : ∀ i, i ∈ O → ∀ c, c ∈ C →
      values c = values i → c ∈ partners i)
    (hN : ∀ i, i ∈ J → ∀ c, c ∈ C → c ∈ partners i →
      (∃ w, w ∈ domains i ∧ w ∈ domains c) → c ∈ N) :
    J.length ≤ N.length + (pool.length - C.length) := by
  let E := O.filter (fun i => !((C.map values).contains (values i)))
  have hcapacity : E.length ≤ pool.length - C.length :=
    SupportBridge212.exception_budget C O pool values hC hO hCpool hOpool
  have hcover :
      ∀ w, w ∈ J.map values → w ∈ N.map values ++ E.map values := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    by_cases hshared : values i ∈ C.map values
    · obtain ⟨c, hc, heq⟩ := List.mem_map.mp hshared
      have hp := hpartners i (hJO i hi) c hc heq
      have hci : values i ∈ domains c := by
        simpa [heq] using hfit c
      have hn := hN i hi c hc hp ⟨values i, hfit i, hci⟩
      exact List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨c, hn, heq⟩))
    · have hiE : i ∈ E := by
        exact List.mem_filter.mpr ⟨hJO i hi, by simpa using hshared⟩
      exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨i, hiE, rfl⟩))
  have hbound :=
    Capacity209.distinct_length_le
      (J.map values) (N.map values ++ E.map values) hJ hcover
  have hlength : J.length ≤ N.length + E.length := by
    simpa using hbound
  omega

#print axioms partner_subset_capacity

end PartnerSubset212
