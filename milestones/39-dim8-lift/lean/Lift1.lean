import Snake9Core
import Sums
import Bits
/-! Part 1: a snake as a function `V : Nat → Nat`, its steps, and the least-used direction. -/
set_option linter.deprecated false
namespace Dim8Lift
open Snake9

def V {M : Nat} (q : Snake M) (t : Nat) : Nat :=
  if h : t ≤ M then (q.vertex ⟨t, by omega⟩).val else 0

theorem V_lt {M : Nat} (q : Snake M) (t : Nat) : V q t < 512 := by
  unfold V; split
  · exact (q.vertex _).isLt
  · omega

theorem V_step {M : Nat} (q : Snake M) {t : Nat} (ht : t < M) :
    ∃ k, k < 9 ∧ V q (t + 1) = V q t ^^^ 2 ^ k := by
  have h := (q.induced ⟨t, by omega⟩ ⟨t + 1, by omega⟩ (by simp)).mpr rfl
  obtain ⟨k, hk, e⟩ := (adj_iff_coordinate_flip _ _).mp h
  refine ⟨k, hk, ?_⟩
  unfold V; rw [dif_pos (by omega), dif_pos (by omega)]; exact e

theorem V_inj {M : Nat} (q : Snake M) {t t' : Nat} (ht : t ≤ M) (ht' : t' ≤ M) (e : V q t = V q t') : t = t' := by
  unfold V at e; rw [dif_pos ht, dif_pos ht'] at e
  have := q.distinct ⟨t, by omega⟩ ⟨t', by omega⟩ (Fin.ext e)
  exact congrArg Fin.val this

/-- Two snake vertices that differ in one coordinate are consecutive. -/
theorem V_adj {M : Nat} (q : Snake M) {t t' k : Nat} (ht : t ≤ M) (ht' : t' ≤ M) (hk : k < 9)
    (e : V q t' = V q t ^^^ 2 ^ k) : t' = t + 1 ∨ t = t' + 1 := by
  have hne : t ≠ t' := by
    intro h; subst h; exact q9_ne0 (V_lt q t) hk e.symm
  have hv : ∀ a b : Nat, (ha : a ≤ M) → (hb : b ≤ M) → V q b = V q a ^^^ 2 ^ k →
      Adj (q.vertex ⟨a, by omega⟩) (q.vertex ⟨b, by omega⟩) := by
    intro a b ha hb eab
    apply (adj_iff_coordinate_flip _ _).mpr
    refine ⟨k, hk, ?_⟩
    unfold V at eab; rw [dif_pos ha, dif_pos hb] at eab; exact eab
  by_cases hlt : t < t'
  · have := (q.induced ⟨t, by omega⟩ ⟨t', by omega⟩ hlt).mp (hv t t' ht ht' e)
    left; simpa using this.symm
  · have e' : V q t = V q t' ^^^ 2 ^ k := by
      rw [e, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have := (q.induced ⟨t', by omega⟩ ⟨t, by omega⟩ (by simp; omega)).mp (hv t' t ht' ht e')
    right; simpa using this.symm

theorem bne_symm (x y : Bool) : (x != y) = (y != x) := by cases x <;> cases y <;> rfl
theorem beq_symm_nat (i k : Nat) : (i == k) = (k == i) := by
  by_cases h : i = k
  · subst h; rfl
  · have h1 : (i == k) = false := by simp [h]
    have h2 : (k == i) = false := by simp [Ne.symm h]
    rw [h1, h2]

def dif {M : Nat} (q : Snake M) (i t : Nat) : Bool := (V q t).testBit i != (V q (t + 1)).testBit i

theorem sum_dif_step {M : Nat} (q : Snake M) {t : Nat} (ht : t < M) :
    sm 9 (fun i => if dif q i t then 1 else 0) = 1 := by
  obtain ⟨k, hk, e⟩ := V_step q ht
  have : ∀ i, i < 9 → (if dif q i t then 1 else 0) = (if k == i then 1 else 0) := by
    intro i hi
    have h := bit_flip hi (V_lt q t) hk
    unfold dif; rw [e]
    have : ((V q t).testBit i != (V q t ^^^ 2 ^ k).testBit i) = (k == i) := by
      rw [bne_symm, h, beq_symm_nat]
    rw [this]
  rw [sm_congr this, sm_single 9 k 1 hk]

theorem sum_dif {M : Nat} (q : Snake M) : ∀ n, n ≤ M → sm 9 (fun i => cnt n (dif q i)) = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have : sm 9 (fun i => cnt (n + 1) (dif q i)) =
        sm 9 (fun i => cnt n (dif q i)) + sm 9 (fun i => if dif q i n then 1 else 0) := by
      rw [← sm_add]; rfl
    rw [this, ih (by omega), sum_dif_step q (by omega)]

theorem sm9_ge (f : Nat → Nat) (h : ∀ i, i < 9 → 26 ≤ f i) : 234 ≤ sm 9 f := by
  have := sm_le_mono (n := 9) (f := fun _ => 26) (g := f) h
  simpa using this

/-- Some direction is used at most 25 times by a snake with at most 233 edges. -/
theorem exists_dir {M : Nat} (q : Snake M) (hM : M ≤ 233) : ∃ i, i < 9 ∧ cnt M (dif q i) ≤ 25 := by
  apply Classical.byContradiction
  intro h
  have h' : ∀ i, i < 9 → 26 ≤ cnt M (dif q i) := by
    intro i hi; apply Classical.byContradiction; intro hc; exact h ⟨i, hi, by omega⟩
  have := sm9_ge _ h'
  rw [sum_dif q M (Nat.le_refl _)] at this; omega

end Dim8Lift
