import Lift2
/-! Part 3: runs of the half inside the prefix, and a level function bounded by 57. -/
set_option linter.deprecated false
namespace Dim8Lift
open Snake9

def sR (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => if p t then sR p t else t + 1

theorem sR_le (p : Nat → Bool) : ∀ t, sR p t ≤ t
  | 0 => Nat.le_refl _
  | t + 1 => by
    unfold sR; split
    · have := sR_le p t; omega
    · exact Nat.le_refl _

theorem sR_in (p : Nat → Bool) : ∀ t s, sR p t ≤ s → s < t → p s = true
  | 0, s, _, h => absurd h (by omega)
  | t + 1, s, h1, h2 => by
    unfold sR at h1
    by_cases hp : p t = true
    · rw [if_pos hp] at h1
      by_cases e : s = t
      · subst e; exact hp
      · exact sR_in p t s h1 (by omega)
    · rw [if_neg hp] at h1; omega

theorem sR_step (p : Nat → Bool) (t : Nat) (h : p t = true) : sR p (t + 1) = sR p t := by
  show (if p t then sR p t else t + 1) = sR p t
  rw [if_pos h]

variable {M : Nat} (q : Snake M) (i : Nat) (b : Bool) (j1 : Nat)

def inP (t : Nat) : Bool := decide (t ≤ j1) && yy q i b t
def inQ (s : Nat) : Bool := decide (s ≤ j1) && inP q i b j1 (j1 - s)
def eR (t : Nat) : Nat := j1 - sR (inQ q i b j1) (j1 - t)
def lv (t : Nat) : Nat := min (t - sR (inP q i b j1) t) (eR q i b j1 t - t)

variable {q i b j1}

theorem eR_ge {t : Nat} (ht : t ≤ j1) : t ≤ eR q i b j1 t := by
  unfold eR; have := sR_le (inQ q i b j1) (j1 - t); omega

theorem eR_in {t s : Nat} (ht : t ≤ j1) (h1 : t < s) (h2 : s ≤ eR q i b j1 t) : inP q i b j1 s = true := by
  unfold eR at h2
  have hle := sR_le (inQ q i b j1) (j1 - t)
  have := sR_in (inQ q i b j1) (j1 - t) (j1 - s) (by omega) (by omega)
  unfold inQ at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  have e : j1 - (j1 - s) = s := by omega
  rw [e] at this; exact this.2

theorem eR_step {t : Nat} (ht : t + 1 ≤ j1) (h : inP q i b j1 (t + 1) = true) :
    eR q i b j1 t = eR q i b j1 (t + 1) := by
  unfold eR
  have e : j1 - t = (j1 - (t + 1)) + 1 := by omega
  rw [e, sR_step]
  unfold inQ; simp only [Bool.and_eq_true, decide_eq_true_eq]
  have e2 : j1 - (j1 - (t + 1)) = t + 1 := by omega
  rw [e2]; exact ⟨by omega, h⟩

theorem inP_yy {t : Nat} (h : inP q i b j1 t = true) : t ≤ j1 ∧ yy q i b t = true := by
  unfold inP at h; simpa using h

theorem inP_of {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) : inP q i b j1 t = true := by
  unfold inP; simp [ht, hy]

theorem cnt_block (p : Nat → Bool) (a e : Nat) (h : ∀ s, a ≤ s → s ≤ e → p s = true) :
    ∀ n, n ≤ e + 1 → n - a ≤ cnt n p := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn; rw [cnt_succ]
    by_cases han : a ≤ n
    · rw [if_pos (h n han (by omega))]; have := ih (by omega); omega
    · have := ih (by omega); omega

theorem cnt_inP_eq : cnt (j1 + 1) (inP q i b j1) = cnt (j1 + 1) (yy q i b) := by
  unfold cnt; apply sm_congr; intro t ht
  unfold inP; simp [show t ≤ j1 by omega]

/-- Runs have at most `cnt (j1+1) yy` vertices, so the level is at most half of that. -/
theorem lv_bound {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) :
    2 * lv q i b j1 t + 1 ≤ cnt (j1 + 1) (yy q i b) := by
  rw [← cnt_inP_eq]
  have hs := sR_le (inP q i b j1) t
  have he := eR_ge (q := q) (i := i) (b := b) ht
  have heq : eR q i b j1 t ≤ j1 := by unfold eR; omega
  have blk := cnt_block (inP q i b j1) (sR (inP q i b j1) t) (eR q i b j1 t) (by
    intro s h1 h2
    by_cases e1 : s < t
    · exact sR_in _ t s h1 e1
    · by_cases e2 : s = t
      · subst e2; exact inP_of ht hy
      · exact eR_in ht (by omega) h2) (eR q i b j1 t + 1) (Nat.le_refl _)
  have mono := cnt_mono (inP q i b j1) (show eR q i b j1 t + 1 ≤ j1 + 1 by omega)
  unfold lv; rw [Nat.min_def]; split <;> omega

end Dim8Lift
