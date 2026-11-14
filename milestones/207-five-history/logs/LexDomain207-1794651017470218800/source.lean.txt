import Std

/-!
General lexicographic representative and pruning arguments.
Compilation receipts are stored separately from this source.

The theorems concern ordinary lexicographic comparison of natural-number lists.
Concrete coordinate actions, their finite orbit enumeration, model invariance,
domain-pre fixedness, and native-search integration remain separate duties.
No geometric isometry or finite search result is assumed proved by this file.
-/

namespace LexDomain207

def LexLE : List Nat → List Nat → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: xs, b :: ys => a < b ∨ (a = b ∧ LexLE xs ys)

theorem lex_refl (xs : List Nat) : LexLE xs xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih => exact Or.inr ⟨rfl, ih⟩

theorem lex_total (xs : List Nat) :
    ∀ ys, LexLE xs ys ∨ LexLE ys xs := by
  induction xs with
  | nil =>
      intro ys
      exact Or.inl True.intro
  | cons a xs ih =>
      intro ys
      cases ys with
      | nil => exact Or.inr True.intro
      | cons b ys =>
          by_cases hab : a < b
          · exact Or.inl (Or.inl hab)
          · by_cases hba : b < a
            · exact Or.inr (Or.inl hba)
            · have heq : a = b := by omega
              rcases ih ys with hxy | hyx
              · exact Or.inl (Or.inr ⟨heq, hxy⟩)
              · exact Or.inr (Or.inr ⟨heq.symm, hyx⟩)

theorem lex_trans (xs : List Nat) :
    ∀ ys zs, LexLE xs ys → LexLE ys zs → LexLE xs zs := by
  induction xs with
  | nil =>
      intro ys zs hxy hyz
      trivial
  | cons a xs ih =>
      intro ys zs hxy hyz
      cases ys with
      | nil => exact False.elim hxy
      | cons b ys =>
          cases zs with
          | nil => exact False.elim hyz
          | cons c zs =>
              change a < b ∨ (a = b ∧ LexLE xs ys) at hxy
              change b < c ∨ (b = c ∧ LexLE ys zs) at hyz
              change a < c ∨ (a = c ∧ LexLE xs zs)
              rcases hxy with hab | ⟨hab, htail₁⟩
              · rcases hyz with hbc | ⟨hbc, htail₂⟩
                · exact Or.inl (by omega)
                · exact Or.inl (by omega)
              · rcases hyz with hbc | ⟨hbc, htail₂⟩
                · exact Or.inl (by omega)
                · exact Or.inr ⟨hab.trans hbc, ih ys zs htail₁ htail₂⟩

/-- Every nonempty finite family has a lexicographic minimum. No action or
orbit assumptions are required for this finite-order statement. -/
theorem finite_minimum (family : List (List Nat)) :
    family ≠ [] →
      ∃ least, least ∈ family ∧ ∀ y, y ∈ family → LexLE least y := by
  induction family with
  | nil =>
      intro hne
      exact False.elim (hne rfl)
  | cons x xs ih =>
      intro hne
      by_cases hnil : xs = []
      · subst xs
        refine ⟨x, by simp, ?_⟩
        intro y hy
        have heq : y = x := List.mem_singleton.mp hy
        subst y
        exact lex_refl x
      · obtain ⟨least, hleast, hminimal⟩ := ih hnil
        rcases lex_total x least with hx | hleastx
        · refine ⟨x, by simp, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with heq | hy
          · subst y
            exact lex_refl x
          · exact lex_trans x least y hx (hminimal y hy)
        · refine ⟨least, List.mem_cons_of_mem x hleast, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with heq | hy
          · subst y
            exact hleastx
          · exact hminimal y hy

/-- Apply this to each finite orbit once its nonemptiness and closure under
the concrete action list have been established. -/
theorem closed_family_has_leader
    (family : List (List Nat)) (actions : List (Nat → Nat))
    (hne : family ≠ [])
    (hclosed : ∀ xs, xs ∈ family → ∀ pi, pi ∈ actions → xs.map pi ∈ family) :
    ∃ xs, xs ∈ family ∧ ∀ pi, pi ∈ actions → LexLE xs (xs.map pi) := by
  obtain ⟨least, hleast, hminimal⟩ := finite_minimum family hne
  refine ⟨least, hleast, ?_⟩
  intro pi hpi
  exact hminimal (least.map pi) (hclosed least hleast pi hpi)

theorem common_prefix_iff (pre xs ys : List Nat) :
    LexLE (pre ++ xs) (pre ++ ys) ↔ LexLE xs ys := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      simpa [LexLE] using ih

theorem map_fixed_prefix (pi : Nat → Nat) (pre : List Nat) :
    (∀ a, a ∈ pre → pi a = a) → pre.map pi = pre := by
  induction pre with
  | nil =>
      intro hfix
      rfl
  | cons a pre ih =>
      intro hfix
      have ha : pi a = a := hfix a (by simp)
      have htail : ∀ b, b ∈ pre → pi b = b := by
        intro b hb
        exact hfix b (List.mem_cons_of_mem a hb)
      simp only [List.map_cons, ha, ih htail]

/-- If the pre is fixed pointwise, a lex-admissible next value cannot
exceed its image. The map need not be a permutation for this implication. -/
theorem first_value_le_image (pi : Nat → Nat) (pre tail : List Nat)
    (u : Nat)
    (hfix : ∀ a, a ∈ pre → pi a = a)
    (hle : LexLE (pre ++ (u :: tail))
      ((pre ++ (u :: tail)).map pi)) :
    u ≤ pi u := by
  have hmap := map_fixed_prefix pi pre hfix
  have hpref : LexLE (pre ++ (u :: tail))
      (pre ++ (pi u :: tail.map pi)) := by
    simpa only [List.map_append, List.map_cons, hmap] using hle
  have hhead := (common_prefix_iff pre (u :: tail)
    (pi u :: tail.map pi)).mp hpref
  change u < pi u ∨ (u = pi u ∧ LexLE tail (tail.map pi)) at hhead
  rcases hhead with hlt | ⟨heq, htail⟩ <;> omega

/-- The exact domain deletion used by the proposed scan preserves any
lex-admissible assignment with a fixed earlier pre. -/
theorem filtered_domain_preserves (pi : Nat → Nat)
    (pre tail domain : List Nat) (u : Nat)
    (hmem : u ∈ domain)
    (hfix : ∀ a, a ∈ pre → pi a = a)
    (hle : LexLE (pre ++ (u :: tail))
      ((pre ++ (u :: tail)).map pi)) :
    u ∈ domain.filter (fun v => decide (v ≤ pi v)) := by
  have hu := first_value_le_image pi pre tail u hfix hle
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  simp [hu]

#print axioms lex_refl
#print axioms lex_total
#print axioms lex_trans
#print axioms finite_minimum
#print axioms closed_family_has_leader
#print axioms first_value_le_image
#print axioms filtered_domain_preserves

end LexDomain207
