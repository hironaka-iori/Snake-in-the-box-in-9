import Std

/-!
General indexed product-cube criterion. Compilation receipts are stored
separately from this source.

The word representation is a list of Boolean coordinates. Fixed lengths are
explicit hypotheses, so concatenation represents a product of two actual cubes.
No isometry assumption is made about the indexed block words.

This file does not connect the saved bitset tables to their geometric meaning.
In particular, it does not certify interval construction, normalization, source
data, finite search coverage, or any of the 70 concrete models.
-/

namespace IndexedCriterion206

abbrev Word := List Bool

/-- On equal-length words, this counts exactly the differing coordinates.
The unequal-length cases make the recursion total; cube statements below
require a common length. -/
def hamming : Word → Word → Nat
  | [], ys => ys.length
  | _ :: xs, [] => xs.length + 1
  | x :: xs, y :: ys => (if x = y then 0 else 1) + hamming xs ys

theorem hamming_eq_zero_iff (u v : Word) : hamming u v = 0 ↔ u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp [hamming]
  | cons bit us ih =>
      cases v with
      | nil => simp [hamming]
      | cons bit' vs =>
          by_cases h : bit = bit'
          · subst bit'
            simp [hamming, ih]
          · simp [hamming, h]

theorem pair_graph_iff (u v : Word) (consecutive : Prop)
    [Decidable consecutive] :
    (if consecutive then hamming u v = 1 else 2 ≤ hamming u v) ↔
      (u ≠ v ∧ (hamming u v = 1 ↔ consecutive)) := by
  have hneq : u ≠ v ↔ hamming u v ≠ 0 :=
    not_congr (hamming_eq_zero_iff u v).symm
  rw [hneq]
  by_cases hc : consecutive <;> simp [hc] <;> omega

/-- Hamming distance adds across aligned coordinate blocks. -/
theorem hamming_append (a b u v : Word) (hab : a.length = b.length) :
    hamming (a ++ u) (b ++ v) = hamming a b + hamming u v := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => simp [hamming]
      | cons bit bs => simp at hab
  | cons bit as ih =>
      cases b with
      | nil => simp at hab
      | cons bit' bs =>
          have htail : as.length = bs.length := Nat.succ.inj hab
          simp only [List.cons_append, hamming]
          rw [ih bs htail]
          exact (Nat.add_assoc _ _ _).symm

/-- The indexed distance definition of an induced path in a cube of width
`width`. The index type can be empty; the application uses 99 indices. -/
def IndexedCubePath {N : Nat} (width : Nat) (p : Fin N → Word) : Prop :=
  (∀ i, (p i).length = width) ∧
  ∀ (i j : Fin N), i.val < j.val →
    if j.val = i.val + 1 then hamming (p i) (p j) = 1
    else 2 ≤ hamming (p i) (p j)

theorem indexed_graph_iff {N width : Nat} (p : Fin N → Word) :
    IndexedCubePath width p ↔
      ((∀ i, (p i).length = width) ∧
        ∀ (i j : Fin N), i.val < j.val →
          p i ≠ p j ∧ (hamming (p i) (p j) = 1 ↔ j.val = i.val + 1)) := by
  constructor
  · intro hp
    exact ⟨hp.1, fun i j hij => (pair_graph_iff (p i) (p j) _).1 (hp.2 i j hij)⟩
  · intro hp
    exact ⟨hp.1, fun i j hij => (pair_graph_iff (p i) (p j) _).2 (hp.2 i j hij)⟩

/-- Exact pair conditions expressed in separate base and block distances. -/
def ProductPairConditions {N : Nat} (z u : Fin N → Word) : Prop :=
  ∀ (i j : Fin N), i.val < j.val →
    if j.val = i.val + 1 then
      hamming (z i) (z j) + hamming (u i) (u j) = 1
    else 2 ≤ hamming (z i) (z j) + hamming (u i) (u j)

/-- The product-cube criterion is necessary and sufficient for arbitrary
indexed block words of the specified width. -/
theorem indexed_product_iff {N baseWidth blockWidth : Nat}
    (z u : Fin N → Word)
    (hz : ∀ i, (z i).length = baseWidth)
    (hu : ∀ i, (u i).length = blockWidth) :
    IndexedCubePath (baseWidth + blockWidth) (fun i => z i ++ u i) ↔
      ProductPairConditions z u := by
  constructor
  · intro hp i j hij
    have h := hp.2 i j hij
    have hadd := hamming_append (z i) (z j) (u i) (u j)
      ((hz i).trans (hz j).symm)
    rw [hadd] at h
    exact h
  · intro hp
    constructor
    · intro i
      simp only [List.length_append, hz i, hu i]
    · intro i j hij
      have hadd := hamming_append (z i) (z j) (u i) (u j)
        ((hz i).trans (hz j).symm)
      rw [hadd]
      exact hp i j hij

/-- Arithmetic form of the exact case distinction used by the native model.
For nonconsecutive indices, base distances at least two require no restriction
on block distance. For consecutive indices, only base distances zero and one
can occur. -/
theorem distance_cases (baseDistance blockDistance : Nat)
    (consecutive : Prop) [Decidable consecutive] :
    (if consecutive then baseDistance + blockDistance = 1
      else 2 ≤ baseDistance + blockDistance) ↔
    (if consecutive then
      (baseDistance = 0 ∧ blockDistance = 1) ∨
        (baseDistance = 1 ∧ blockDistance = 0)
     else
      (baseDistance = 0 → 2 ≤ blockDistance) ∧
        (baseDistance = 1 → 1 ≤ blockDistance)) := by
  by_cases h : consecutive
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

/-- Substitution through an arbitrary index-to-variable map is sound once
every indexed pair condition has been supplied. The map need not be injective:
pairs mapped to the same variable remain among the hypotheses. -/
theorem interval_substitution_sound {N M baseWidth blockWidth : Nat}
    (z : Fin N → Word) (group : Fin N → Fin M) (values : Fin M → Word)
    (hz : ∀ i, (z i).length = baseWidth)
    (hv : ∀ a, (values a).length = blockWidth)
    (hpairs : ProductPairConditions z (fun i => values (group i))) :
    IndexedCubePath (baseWidth + blockWidth)
      (fun i => z i ++ values (group i)) := by
  exact (indexed_product_iff z (fun i => values (group i))
    hz (fun i => hv (group i))).2 hpairs

/-- A generic relation-table soundness interface. `hcover` is an explicit
geometric obligation for every original indexed pair, including pairs mapped
to the same variable. This theorem does not discharge that obligation for any
generated table. Unconstrained variable pairs may use the universal relation. -/
theorem relation_substitution_sound {N M baseWidth blockWidth : Nat}
    (z : Fin N → Word) (group : Fin N → Fin M) (values : Fin M → Word)
    (R : Fin M → Fin M → Word → Word → Prop)
    (hz : ∀ i, (z i).length = baseWidth)
    (hv : ∀ a, (values a).length = blockWidth)
    (hcover : ∀ (i j : Fin N), i.val < j.val → ∀ (u v : Word),
      R (group i) (group j) u v →
        if j.val = i.val + 1 then
          hamming (z i) (z j) + hamming u v = 1
        else 2 ≤ hamming (z i) (z j) + hamming u v)
    (hsatisfies : ∀ a b, R a b (values a) (values b)) :
    IndexedCubePath (baseWidth + blockWidth)
      (fun i => z i ++ values (group i)) := by
  apply interval_substitution_sound z group values hz hv
  intro i j hij
  exact hcover i j hij (values (group i)) (values (group j))
    (hsatisfies (group i) (group j))

#print axioms hamming_append
#print axioms hamming_eq_zero_iff
#print axioms pair_graph_iff
#print axioms indexed_graph_iff
#print axioms indexed_product_iff
#print axioms distance_cases
#print axioms interval_substitution_sound
#print axioms relation_substitution_sound

end IndexedCriterion206
