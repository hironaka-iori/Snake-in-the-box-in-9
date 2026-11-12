import LayerJoining
namespace BlockReplacement193
open LayerJoining

/-- Replace a block without changing its length or the outside positions. -/
def replaceBlock {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n+1) → V) (a b : Nat)
    (hout : ∀ i, i.val ≤ a ∨ b ≤ i.val → q i = p.vertex i)
    (hinj : ∀ i j, a ≤ i.val → i.val ≤ b → a ≤ j.val → j.val ≤ b →
      q i = q j → i = j)
    (hedge : ∀ i j, a ≤ i.val → j.val ≤ b → i.val < j.val →
      (R (q i) (q j) ↔ i.val+1=j.val))
    (hdis : ∀ i j, a < i.val → i.val < b →
      (j.val ≤ a ∨ b ≤ j.val) → q i ≠ p.vertex j)
    (hsep : ∀ i j, a < i.val → i.val < b →
      (j.val < a ∨ b < j.val) →
      ¬ R (q i) (p.vertex j) ∧ ¬ R (p.vertex j) (q i)) :
    InducedPath V R n where
  vertex := q
  distinct i j he := by
    by_cases hi : a < i.val ∧ i.val < b
    · by_cases hj : a < j.val ∧ j.val < b
      · exact hinj i j (by omega) (by omega) (by omega) (by omega) he
      · have hjout : j.val ≤ a ∨ b ≤ j.val := by omega
        rw [hout j hjout] at he
        exact False.elim (hdis i j hi.1 hi.2 hjout he)
    · have hiout : i.val ≤ a ∨ b ≤ i.val := by omega
      by_cases hj : a < j.val ∧ j.val < b
      · rw [hout i hiout] at he
        exact False.elim (hdis j i hj.1 hj.2 hiout he.symm)
      · rw [hout i hiout, hout j (by omega)] at he
        exact p.distinct i j he
  induced i j hij := by
    by_cases hi : a < i.val ∧ i.val < b
    · by_cases hj : j.val ≤ b
      · exact hedge i j (by omega) hj hij
      · have hjout : b ≤ j.val := by omega
        have hn := (hsep i j hi.1 hi.2 (Or.inr (by omega))).1
        rw [hout j (Or.inr hjout)]
        constructor
        · intro h; exact False.elim (hn h)
        · intro h; omega
    · by_cases hj : a < j.val ∧ j.val < b
      · by_cases hia : a ≤ i.val
        · exact hedge i j hia (by omega) hij
        · have hiout : i.val ≤ a := by omega
          have hn := (hsep j i hj.1 hj.2 (Or.inl (by omega))).2
          rw [hout i (Or.inl hiout)]
          constructor
          · intro h; exact False.elim (hn h)
          · intro h; omega
      · rw [hout i (by omega), hout j (by omega)]
        exact p.induced i j hij

/-- A closed family stays closed along every finite chain of allowed moves. -/
theorem finiteChain {V : Type} (B : V → Prop) (S : V → V → Prop)
    (closed : ∀ x y, B x → S x y → B y)
    (x : Nat → V) (n : Nat) (hstart : B (x 0))
    (hstep : ∀ k, k < n → S (x k) (x (k+1))) : B (x n) := by
  have hmem : ∀ k, k ≤ n → B (x k) := by
    intro k
    induction k with
    | zero => intro _; exact hstart
    | succ k ih =>
      intro hk
      exact closed (x k) (x (k+1)) (ih (by omega)) (hstep k (by omega))
  exact hmem n (by omega)

theorem noExtensionAfterChain {V : Type} (B : V → Prop) (S : V → V → Prop)
    (E : V → Prop) (closed : ∀ x y, B x → S x y → B y)
    (blocked : ∀ x, B x → ¬ E x)
    (x : Nat → V) (n : Nat) (hstart : B (x 0))
    (hstep : ∀ k, k < n → S (x k) (x (k+1))) : ¬ E (x n) := by
  exact blocked (x n) (finiteChain B S closed x n hstart hstep)

#print axioms replaceBlock
#print axioms finiteChain
#print axioms noExtensionAfterChain
end BlockReplacement193
