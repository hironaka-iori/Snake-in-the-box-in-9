import PartnerSubset212

/-!
Source prepared for checking; not compiled by its author.
Tight partner capacity consumes both the listed partner words and the
entire exception budget. Geometry, domain masks and traversal are separate.
-/

namespace TightPartner214

private theorem equal_values_same_identifier (xs : List Nat)
    (values : Nat → Nat) (hn : (xs.map values).Nodup) :
    ∀ x, x ∈ xs → ∀ y, y ∈ xs → values x = values y → x = y := by
  revert hn
  induction xs with
  | nil =>
      intro _ x hx
      exact False.elim (List.not_mem_nil hx)
  | cons a xs ih =>
      intro hn x hx y hy heq
      have hp : values a ∉ xs.map values ∧ (xs.map values).Nodup := by
        simpa using hn
      rcases List.mem_cons.mp hx with hxa | hx
      · subst x
        rcases List.mem_cons.mp hy with hya | hy
        · exact hya.symm
        · exact False.elim (hp.1 (List.mem_map.mpr ⟨y, hy, heq.symm⟩))
      · rcases List.mem_cons.mp hy with hya | hy
        · subst y
          exact False.elim (hp.1 (List.mem_map.mpr ⟨x, hx, heq⟩))
        · exact ih hp.2 x hx y hy heq

/-- Equality in partner-subset capacity forces every remaining outside
variable to share with a chosen variable outside N. N may overestimate
the partners of J; inclusion in C is unnecessary for this implication. -/
theorem tight_subset_forces_external_sharing
    (C O pool J N : List Nat) (values : Nat → Nat)
    (hC : (C.map values).Nodup)
    (hO : (O.map values).Nodup)
    (hJ : (J.map values).Nodup)
    (hCpool : ∀ c, c ∈ C → values c ∈ pool)
    (hOpool : ∀ i, i ∈ O → values i ∈ pool)
    (hJO : ∀ i, i ∈ J → i ∈ O)
    (hN : ∀ i, i ∈ J → ∀ c, c ∈ C →
      values c = values i → c ∈ N)
    (htight : J.length = N.length + (pool.length - C.length)) :
    ∀ x, x ∈ O → x ∉ J →
      ∃ c, c ∈ C ∧ c ∉ N ∧ values c = values x := by
  let E := O.filter (fun i => !((C.map values).contains (values i)))
  have hcapacity : E.length ≤ pool.length - C.length :=
    SupportBridge212.exception_budget C O pool values hC hO hCpool hOpool
  have hcover :
      ∀ w, w ∈ J.map values → w ∈ N.map values ++ E.map values := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    by_cases hs : values i ∈ C.map values
    · obtain ⟨c, hc, heq⟩ := List.mem_map.mp hs
      exact List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨c, hN i hi c hc heq, heq⟩))
    · have hiE : i ∈ E := by
        exact List.mem_filter.mpr ⟨hJO i hi, by simpa using hs⟩
      exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨i, hiE, rfl⟩))
  have hb := Capacity209.distinct_length_le
    (J.map values) (N.map values ++ E.map values) hJ hcover
  have hbound : J.length ≤ N.length + E.length := by simpa using hb
  have hlength :
      (J.map values).length = (N.map values ++ E.map values).length := by
    simp only [List.length_map, List.length_append]
    omega
  have hused := Capacity209.saturated_covers
    (J.map values) (N.map values ++ E.map values) hJ hcover hlength
  intro x hx hxJ
  have hxunused : values x ∉ J.map values := by
    intro hw
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp hw
    have hix := equal_values_same_identifier O values hO
      i (hJO i hi) x hx heq
    exact hxJ (hix ▸ hi)
  have hnotN : values x ∉ N.map values := by
    intro hw
    exact hxunused (hused (values x) (List.mem_append.mpr (Or.inl hw)))
  have hnotE : values x ∉ E.map values := by
    intro hw
    exact hxunused (hused (values x) (List.mem_append.mpr (Or.inr hw)))
  have hshared : values x ∈ C.map values := by
    by_cases hs : values x ∈ C.map values
    · exact hs
    · have hxE : x ∈ E := by
        exact List.mem_filter.mpr ⟨hx, by simpa using hs⟩
      exact False.elim (hnotE (List.mem_map.mpr ⟨x, hxE, rfl⟩))
  obtain ⟨c, hc, heq⟩ := List.mem_map.mp hshared
  refine ⟨c, hc, ?_, heq⟩
  intro hcN
  exact hnotN (List.mem_map.mpr ⟨c, hcN, heq⟩)

/-- Current-domain partner coverage supplies the tight subset premise.
For an outside variable not in J, retaining only support from partners
outside N preserves the same complete assignment. -/
theorem tight_partner_filter_preserves_assignment
    (C O pool J N support : List Nat) (chosen : Nat)
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
      (∃ w, w ∈ domains i ∧ w ∈ domains c) → c ∈ N)
    (htight : J.length = N.length + (pool.length - C.length))
    (hchosen : chosen ∈ O)
    (hchosenJ : chosen ∉ J)
    (hsupport : ∀ c, c ∈ C → c ∈ partners chosen → c ∉ N →
      ∀ w, w ∈ domains c → w ∈ support) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun w => decide (w ∈ support))
      else domains g) := by
  have hactual : ∀ i, i ∈ J → ∀ c, c ∈ C →
      values c = values i → c ∈ N := by
    intro i hi c hc heq
    have hp := hpartners i (hJO i hi) c hc heq
    have hci : values i ∈ domains c := by simpa [heq] using hfit c
    exact hN i hi c hc hp ⟨values i, hfit i, hci⟩
  obtain ⟨c, hc, hcN, heq⟩ :=
    tight_subset_forces_external_sharing C O pool J N values
      hC hO hJ hCpool hOpool hJO hactual htight chosen hchosen hchosenJ
  have hp := hpartners chosen hchosen c hc heq
  have hs : values chosen ∈ support := by
    have hw := hsupport c hc hp hcN (values c) (hfit c)
    exact heq ▸ hw
  intro g
  by_cases hg : g = chosen
  · subst g
    simpa [hs] using hfit chosen
  · simpa [hg] using hfit g

#print axioms tight_subset_forces_external_sharing
#print axioms tight_partner_filter_preserves_assignment

end TightPartner214
