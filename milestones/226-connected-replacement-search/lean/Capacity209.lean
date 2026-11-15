import Std

/-!
Written source draft; not compiled by its author.

These finite-list statements support necessary capacity and saturation
consequences. They do not certify cube geometry, concrete interval counts,
native domain masks, pruning integration, or a search exclusion.
-/

namespace Capacity209

private def removeOne (value : Nat) : List Nat → List Nat
  | [] => []
  | a :: xs => if a = value then xs else a :: removeOne value xs

private theorem other_mem_removeOne (value x : Nat) (pool : List Nat)
    (hne : x ≠ value) : x ∈ pool → x ∈ removeOne value pool := by
  induction pool with
  | nil =>
      intro hx
      exact False.elim (List.not_mem_nil hx)
  | cons a xs ih =>
      intro hx
      by_cases ha : a = value
      · rcases List.mem_cons.mp hx with hxa | htail
        · exact False.elim (hne (hxa.trans ha))
        · simpa [removeOne, ha] using htail
      · rcases List.mem_cons.mp hx with hxa | htail
        · simp only [removeOne, if_neg ha, List.mem_cons]
          exact Or.inl hxa
        · simp only [removeOne, if_neg ha, List.mem_cons]
          exact Or.inr (ih htail)

private theorem removeOne_length (value : Nat) (pool : List Nat) :
    value ∈ pool → (removeOne value pool).length + 1 = pool.length := by
  induction pool with
  | nil =>
      intro hx
      exact False.elim (List.not_mem_nil hx)
  | cons a xs ih =>
      intro hx
      by_cases ha : a = value
      · simp [removeOne, ha]
      · have hva : value ≠ a := Ne.symm ha
        have htail : value ∈ xs := by simpa [hva] using hx
        have hlength := ih htail
        simp only [removeOne, if_neg ha, List.length_cons]
        omega

/-- Distinct selected values inject into any finite list containing them.
Using a duplicate-free list for `pool` gives its actual set cardinality. -/
theorem distinct_length_le (selected : List Nat) :
    ∀ pool : List Nat, selected.Nodup →
      (∀ x, x ∈ selected → x ∈ pool) → selected.length ≤ pool.length := by
  induction selected with
  | nil =>
      intro pool hdistinct hsubset
      simp
  | cons a xs ih =>
      intro pool hdistinct hsubset
      have hparts : a ∉ xs ∧ xs.Nodup := by simpa using hdistinct
      have ha : a ∈ pool := hsubset a (by simp)
      have htail : ∀ x, x ∈ xs → x ∈ removeOne a pool := by
        intro x hx
        have hne : x ≠ a := by
          intro heq
          subst x
          exact hparts.1 hx
        exact other_mem_removeOne a x pool hne
          (hsubset x (List.mem_cons_of_mem a hx))
      have hbound := ih (removeOne a pool) hparts.2 htail
      have hlength := removeOne_length a pool ha
      simp only [List.length_cons]
      omega

/-- If an equally long distinct list is contained in `pool`, it uses every
word of `pool`. This is the finite saturation implication. -/
theorem saturated_covers (selected pool : List Nat)
    (hdistinct : selected.Nodup)
    (hsubset : ∀ x, x ∈ selected → x ∈ pool)
    (hlength : selected.length = pool.length) :
    ∀ word, word ∈ pool → word ∈ selected := by
  intro word hword
  by_cases hselected : word ∈ selected
  · exact hselected
  · have hsmaller : ∀ x, x ∈ selected → x ∈ removeOne word pool := by
      intro x hx
      have hne : x ≠ word := by
        intro heq
        subst x
        exact hselected hx
      exact other_mem_removeOne word x pool hne (hsubset x hx)
    have hbound := distinct_length_le selected (removeOne word pool)
      hdistinct hsmaller
    have hremoved := removeOne_length word pool hword
    omega

/-- To obtain a Hall union-domain bound, use a duplicate-free enumeration
of the union of the selected groups' domains as `pool`. -/
theorem domain_capacity (groups pool : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hdistinct : (groups.map values).Nodup)
    (hfit : ∀ g, g ∈ groups → values g ∈ domains g)
    (hunion : ∀ g, g ∈ groups → ∀ word, word ∈ domains g → word ∈ pool) :
    groups.length ≤ pool.length := by
  have hsubset : ∀ word, word ∈ groups.map values → word ∈ pool := by
    intro word hword
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hword
    exact hunion g hg (values g) (hfit g hg)
  have hbound := distinct_length_le (groups.map values) pool hdistinct hsubset
  simpa using hbound

/-- Under saturation, supply `hused` from `saturated_covers`. If only one
clique domain can contain the word, that clique variable must use it. -/
theorem unique_support_forces (clique : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat) (word chosen : Nat)
    (hused : word ∈ clique.map values)
    (hfit : ∀ g, g ∈ clique → values g ∈ domains g)
    (honly : ∀ g, g ∈ clique → word ∈ domains g → g = chosen) :
    values chosen = word := by
  obtain ⟨g, hg, hvalue⟩ := List.mem_map.mp hused
  have hword : word ∈ domains g := by simpa [hvalue] using hfit g hg
  have hchosen := honly g hg hword
  simpa [hchosen] using hvalue

/-- If all nonpartners in a covering clique conflict with an outside word,
some partner domain must support that word. Geometry supplies `hconflict`. -/
theorem partner_support (clique partners : List Nat)
    (values : Nat → Nat) (domains : Nat → List Nat) (word : Nat)
    (hused : word ∈ clique.map values)
    (hfit : ∀ g, g ∈ clique → values g ∈ domains g)
    (hconflict : ∀ g, g ∈ clique → g ∉ partners → values g ≠ word) :
    ∃ g, g ∈ partners ∧ word ∈ domains g := by
  obtain ⟨g, hg, hvalue⟩ := List.mem_map.mp hused
  have hpartner : g ∈ partners := by
    by_cases hp : g ∈ partners
    · exact hp
    · exact False.elim (hconflict g hg hp hvalue)
  refine ⟨g, hpartner, ?_⟩
  simpa [hvalue] using hfit g hg

#print axioms distinct_length_le
#print axioms saturated_covers
#print axioms domain_capacity
#print axioms unique_support_forces
#print axioms partner_support

end Capacity209
