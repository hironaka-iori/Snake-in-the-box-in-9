import Std

/-!
Written source draft; not compiled by its author.

These are generic domain and coverage statements. They do not certify native
pruning, an implementation's saved vectors, persistence, or concrete exclusions.
For the search application, regions are intersected with one unchanged global
acceptable-assignment predicate, including the original lex inequalities.
-/

namespace Frontier208

universe u v

def Fits {I : Type u} {A : Type v} (domains : I → List A) (x : I → A) : Prop :=
  ∀ i, x i ∈ domains i

def replace {I : Type u} {A : Type v} [DecidableEq I]
    (domains : I → List A) (chosen : I) (values : List A) : I → List A :=
  fun i => if i = chosen then values else domains i

theorem fits_replace_iff {I : Type u} {A : Type v} [DecidableEq I]
    (domains : I → List A) (chosen : I) (values : List A) (x : I → A) :
    Fits (replace domains chosen values) x ↔
      x chosen ∈ values ∧ ∀ i, i ≠ chosen → x i ∈ domains i := by
  constructor
  · intro h
    constructor
    · simpa [replace] using h chosen
    · intro i hi
      simpa [replace, hi] using h i
  · rintro ⟨hchosen, hrest⟩
    intro i
    by_cases hi : i = chosen
    · subst i
      simpa [replace] using hchosen
    · simpa [replace, hi] using hrest i hi

/-- Removing all occurrences gives a disjoint split even if the domain list
contains duplicate values. -/
theorem domain_split {I : Type u} {A : Type v}
    [DecidableEq I] [DecidableEq A]
    (domains : I → List A) (chosen : I) (value : A) (x : I → A)
    (hvalue : value ∈ domains chosen) :
    Fits domains x ↔
      Fits (replace domains chosen [value]) x ∨
      Fits (replace domains chosen
        ((domains chosen).filter (fun a => decide (a ≠ value)))) x := by
  constructor
  · intro h
    by_cases heq : x chosen = value
    · left
      apply (fits_replace_iff domains chosen [value] x).mpr
      constructor
      · simp [heq]
      · intro i hi
        exact h i
    · right
      apply (fits_replace_iff domains chosen
        ((domains chosen).filter (fun a => decide (a ≠ value))) x).mpr
      constructor
      · refine List.mem_filter.mpr ⟨h chosen, ?_⟩
        simp [heq]
      · intro i hi
        exact h i
  · intro h
    rcases h with hchosen | hremaining
    · obtain ⟨hk, hrest⟩ :=
        (fits_replace_iff domains chosen [value] x).mp hchosen
      intro i
      by_cases hi : i = chosen
      · subst i
        have heq : x chosen = value := List.mem_singleton.mp hk
        simpa [heq] using hvalue
      · exact hrest i hi
    · obtain ⟨hk, hrest⟩ :=
        (fits_replace_iff domains chosen
          ((domains chosen).filter (fun a => decide (a ≠ value))) x).mp hremaining
      intro i
      by_cases hi : i = chosen
      · subst i
        exact (List.mem_filter.mp hk).1
      · exact hrest i hi

theorem domain_split_disjoint {I : Type u} {A : Type v}
    [DecidableEq I] [DecidableEq A]
    (domains : I → List A) (chosen : I) (value : A) (x : I → A) :
    ¬ (Fits (replace domains chosen [value]) x ∧
      Fits (replace domains chosen
        ((domains chosen).filter (fun a => decide (a ≠ value)))) x) := by
  rintro ⟨hchosen, hremaining⟩
  have hc := (fits_replace_iff domains chosen [value] x).mp hchosen
  have hr := (fits_replace_iff domains chosen
    ((domains chosen).filter (fun a => decide (a ≠ value))) x).mp hremaining
  have heq : x chosen = value := List.mem_singleton.mp hc.1
  simpa [heq] using hr.1

abbrev Region (A : Type u) := A → Prop

def Covers {A : Type u} (target : Region A)
    (frontier : List (Region A)) : Prop :=
  ∀ x, target x → ∃ region, region ∈ frontier ∧ region x

/-- Replacing one covered region by a covering frontier preserves coverage.
No disjointness premise is needed for this completeness implication. -/
theorem replace_covered_region {A : Type u}
    (target old : Region A)
    (before replacement after : List (Region A))
    (hcover : Covers target (before ++ (old :: after)))
    (hrefine : Covers old replacement) :
    Covers target (before ++ (replacement ++ after)) := by
  intro x hx
  obtain ⟨region, hregion, hrx⟩ := hcover x hx
  rcases List.mem_append.mp hregion with hbefore | htail
  · exact ⟨region, List.mem_append.mpr (Or.inl hbefore), hrx⟩
  · rcases List.mem_cons.mp htail with heq | hafter
    · subst region
      obtain ⟨child, hchild, hcx⟩ := hrefine x hrx
      exact ⟨child, List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hchild))), hcx⟩
    · exact ⟨region, List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hafter))), hrx⟩

/-- A sound exhaustion justification permits replacement by no regions. -/
theorem exhausted_region_cover {A : Type u} (region : Region A)
    (hexhausted : ∀ x, ¬ region x) : Covers region [] := by
  intro x hx
  exact False.elim (hexhausted x hx)

/-- The coverage premise is essential. An empty native queue alone does not
provide this premise or certify an exclusion. -/
theorem empty_frontier_excludes {A : Type u} (target : Region A)
    (hcover : Covers target []) : ¬ ∃ x, target x := by
  rintro ⟨x, hx⟩
  obtain ⟨region, hregion, hrx⟩ := hcover x hx
  exact List.not_mem_nil hregion

#print axioms fits_replace_iff
#print axioms domain_split
#print axioms domain_split_disjoint
#print axioms replace_covered_region
#print axioms exhausted_region_cover
#print axioms empty_frontier_excludes

end Frontier208
