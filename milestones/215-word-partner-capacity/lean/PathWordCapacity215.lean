import ConcreteSupport213
import Subset211

/-!
Source prepared for checking; not compiled by its author.
Only the concrete induced-path premise is used to obtain distinct words.
No initial-value normalization, raw-value bound or parity pool is needed.
-/

set_option Elab.async false

namespace PathWordCapacity215

open ConcreteGeometry213 IndexedCriterion206

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

private theorem subset_words_distinct
    (F J : List Nat) (values : Nat → Nat)
    (hF : (F.map values).Nodup)
    (hJ : J.Nodup)
    (hsubset : ∀ i, i ∈ J → i ∈ F) :
    (J.map values).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem ?_ hJ
  intro a b ha hb hne heq
  exact hne (equal_values_same_identifier F values hF
    a (hsubset a ha) b (hsubset b hb) heq)

/-- Each of the four literal chosen/outside families has distinct raw
assigned words whenever its reconstructed indexed vertices form a path. -/
theorem literal_family_words_distinct
    (F : List Nat) (values : Nat → Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hfamily : F ∈ [chosen0, outside0, chosen1, outside1]) :
    (F.map values).Nodup := by
  have he := ConcreteSupport213.even_support_conditions values hp
  have ho := ConcreteSupport213.odd_support_conditions values hp
  have hc : F = chosen0 ∨ F = outside0 ∨ F = chosen1 ∨ F = outside1 := by
    simpa using hfamily
  rcases hc with rfl | rfl | rfl | rfl
  · exact he.1
  · exact he.2.1
  · exact ho.1
  · exact ho.2.1

/-- A domain pool shorter than a duplicate-free subset of one literal
family contradicts any fitting concrete induced-path assignment. -/
theorem deficient_domain_pool_impossible
    (F J U : List Nat) (values : Nat → Nat) (domains : Nat → List Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hfamily : F ∈ [chosen0, outside0, chosen1, outside1])
    (hJ : J.Nodup)
    (hsubset : ∀ i, i ∈ J → i ∈ F)
    (hfit : ∀ i, values i ∈ domains i)
    (hpool : ∀ i, i ∈ J → ∀ w, w ∈ domains i → w ∈ U)
    (hshort : U.length < J.length) : False := by
  have hF := literal_family_words_distinct F values hp hfamily
  have hd := subset_words_distinct F J values hF hJ hsubset
  exact Subset211.deficient_pool_impossible J U values domains
    hd (fun i _ => hfit i) hpool hshort

/-- A tight domain pool is reserved for its subset. Removing its words
from another member of the same literal family retains the same fitting
assignment at every variable. -/
theorem tight_domain_pool_filter
    (F J U : List Nat) (chosen : Nat)
    (values : Nat → Nat) (domains : Nat → List Nat)
    (hp : IndexedCubePath 8
      (fun i => [(z i).1, (z i).2] ++ ConcreteSupport213.word (values (group i))))
    (hfamily : F ∈ [chosen0, outside0, chosen1, outside1])
    (hJ : J.Nodup)
    (hsubset : ∀ i, i ∈ J → i ∈ F)
    (hfit : ∀ i, values i ∈ domains i)
    (hpool : ∀ i, i ∈ J → ∀ w, w ∈ domains i → w ∈ U)
    (htight : U.length = J.length)
    (hchosen : chosen ∈ F)
    (hchosenJ : chosen ∉ J) :
    ∀ g, values g ∈
      (if g = chosen then
        (domains g).filter (fun w => decide (w ∉ U))
      else domains g) := by
  have hF := literal_family_words_distinct F values hp hfamily
  have hd := subset_words_distinct F J values hF hJ hsubset
  have hconflict : ∀ j, j ∈ J → values chosen ≠ values j := by
    intro j hj heq
    have hc := equal_values_same_identifier F values hF
      chosen hchosen j (hsubset j hj) heq
    exact hchosenJ (hc.symm ▸ hj)
  exact Subset211.pruning_preserves_assignment J U values domains chosen
    hd hfit hpool htight.symm hconflict

#print axioms literal_family_words_distinct
#print axioms deficient_domain_pool_impossible
#print axioms tight_domain_pool_filter

end PathWordCapacity215
