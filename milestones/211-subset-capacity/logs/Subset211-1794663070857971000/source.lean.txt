import Capacity209

/-!
Source prepared for checking; this file's author has not compiled it.

These deductions concern a fixed assignment of natural-number words to
finite-list variables. Distinctness and the domain inclusions are explicit
hypotheses. They do not certify geometric conflicts, native domain masks,
search traversal, or any global snake bound.
-/

namespace Subset211

/-- Distinct assigned words in a saturated union of domains use every
word of that union. A duplicate-free pool gives the actual union size. -/
theorem saturated_subset_covers (groups pool : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hdistinct : (groups.map values).Nodup)
    (hfit : ∀ g, g ∈ groups → values g ∈ domains g)
    (hunion : ∀ g, g ∈ groups → ∀ word, word ∈ domains g → word ∈ pool)
    (hlength : groups.length = pool.length) :
    ∀ word, word ∈ pool → ∃ g, g ∈ groups ∧ values g = word := by
  have hsubset : ∀ word, word ∈ groups.map values → word ∈ pool := by
    intro word hword
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hword
    exact hunion g hg (values g) (hfit g hg)
  have hlength' : (groups.map values).length = pool.length := by
    simpa using hlength
  intro word hword
  exact List.mem_map.mp
    (Capacity209.saturated_covers (groups.map values) pool
      hdistinct hsubset hlength' word hword)

/-- A variable conflicting with every member of a saturated subset
cannot use any word from that subset's pool. -/
theorem outside_not_mem_pool (groups pool : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat) (outside : Nat)
    (hdistinct : (groups.map values).Nodup)
    (hfit : ∀ g, g ∈ groups → values g ∈ domains g)
    (hunion : ∀ g, g ∈ groups → ∀ word, word ∈ domains g → word ∈ pool)
    (hlength : groups.length = pool.length)
    (hconflict : ∀ g, g ∈ groups → values outside ≠ values g) :
    values outside ∉ pool := by
  intro hword
  obtain ⟨g, hg, hvalue⟩ :=
    saturated_subset_covers groups pool values domains
      hdistinct hfit hunion hlength (values outside) hword
  exact hconflict g hg hvalue.symm

/-- Removing the saturated pool from a conflicting variable's domain
preserves the same assignment at every variable. Other constraints on
that assignment are unchanged. -/
theorem pruning_preserves_assignment (groups pool : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat) (outside : Nat)
    (hdistinct : (groups.map values).Nodup)
    (hfit : ∀ g, values g ∈ domains g)
    (hunion : ∀ g, g ∈ groups → ∀ word, word ∈ domains g → word ∈ pool)
    (hlength : groups.length = pool.length)
    (hconflict : ∀ g, g ∈ groups → values outside ≠ values g) :
    ∀ g, values g ∈
      (if g = outside then
        (domains g).filter (fun word => decide (word ∉ pool))
      else domains g) := by
  have hnot : values outside ∉ pool :=
    outside_not_mem_pool groups pool values domains outside
      hdistinct (fun g _ => hfit g) hunion hlength hconflict
  intro g
  by_cases hg : g = outside
  · subst g
    simpa [hnot] using hfit outside
  · simpa [hg] using hfit g

/-- Fewer available pool words than pairwise distinct assigned variables
contradicts any assignment satisfying the stated domains. -/
theorem deficient_pool_impossible (groups pool : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hdistinct : (groups.map values).Nodup)
    (hfit : ∀ g, g ∈ groups → values g ∈ domains g)
    (hunion : ∀ g, g ∈ groups → ∀ word, word ∈ domains g → word ∈ pool)
    (hshort : pool.length < groups.length) : False := by
  have hbound :=
    Capacity209.domain_capacity groups pool values domains hdistinct hfit hunion
  omega

#print axioms saturated_subset_covers
#print axioms outside_not_mem_pool
#print axioms pruning_preserves_assignment
#print axioms deficient_pool_impossible

end Subset211
