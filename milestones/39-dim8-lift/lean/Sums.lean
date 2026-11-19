/-! Finite sums and counts over `[0, n)` by recursion (core Lean only). -/
namespace Dim8Lift

def sm : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sm n f + f n

def cnt (n : Nat) (p : Nat → Bool) : Nat := sm n (fun t => if p t then 1 else 0)

@[simp] theorem sm_zero (f : Nat → Nat) : sm 0 f = 0 := rfl
@[simp] theorem sm_succ (n : Nat) (f : Nat → Nat) : sm (n + 1) f = sm n f + f n := rfl
theorem cnt_succ (n : Nat) (p : Nat → Bool) :
    cnt (n + 1) p = cnt n p + (if p n then 1 else 0) := rfl
@[simp] theorem cnt_zero (p : Nat → Bool) : cnt 0 p = 0 := rfl

theorem sm_congr {n : Nat} {f g : Nat → Nat} (h : ∀ t, t < n → f t = g t) : sm n f = sm n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sm_succ]
    rw [ih (fun t ht => h t (by omega)), h n (by omega)]

theorem sm_add (n : Nat) (f g : Nat → Nat) : sm n (fun t => f t + g t) = sm n f + sm n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sm_succ, ih]; omega

theorem sm_zero_fun (n : Nat) : sm n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

theorem sm_mul_const (n : Nat) (f : Nat → Nat) (c : Nat) :
    sm n (fun t => c * f t) = c * sm n f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sm_succ, ih, Nat.mul_add]

theorem sm_comm (N T : Nat) (h : Nat → Nat → Nat) :
    sm N (fun u => sm T (fun t => h u t)) = sm T (fun t => sm N (fun u => h u t)) := by
  induction T with
  | zero => simp [sm_zero_fun]
  | succ T ih =>
    simp only [sm_succ]
    rw [sm_add, ih]

theorem sm_le_mono {n : Nat} {f g : Nat → Nat} (h : ∀ t, t < n → f t ≤ g t) : sm n f ≤ sm n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sm_succ]
    have := ih (fun t ht => h t (by omega)); have := h n (by omega); omega

theorem sm_single (N c x : Nat) (hc : c < N) :
    sm N (fun u => if c == u then x else 0) = x := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [sm_succ]
    by_cases h : c = N
    · subst h
      have : sm c (fun u => if c == u then x else 0) = 0 := by
        rw [sm_congr (g := fun _ => 0)]; exact sm_zero_fun _
        intro t ht; have : (c == t) = false := by simp; omega
        simp [this]
      rw [this, beq_self_eq_true]; simp
    · rw [ih (by omega)]; have : (c == N) = false := by simp [h]
      rw [this]; simp

theorem cnt_le_one {T : Nat} {p : Nat → Bool} (h : ∀ t t', t < T → t' < T → p t = true → p t' = true → t = t') :
    cnt T p ≤ 1 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [cnt_succ]
    by_cases hp : p T = true
    · have : cnt T p = 0 := by
        have hz : ∀ t, t < T → p t = false := by
          intro t ht; cases hpt : p t
          · rfl
          · exact absurd (h t T (by omega) (by omega) hpt hp) (by omega)
        unfold cnt; rw [sm_congr (g := fun _ => 0)]; exact sm_zero_fun _
        intro t ht; simp [hz t ht]
      simp [hp, this]
    · have := ih (fun t t' ht ht' => h t t' (by omega) (by omega)); simp [hp]; omega

theorem cnt_pos {T : Nat} {p : Nat → Bool} {t : Nat} (ht : t < T) (hp : p t = true) : 1 ≤ cnt T p := by
  induction T with
  | zero => omega
  | succ T ih =>
    rw [cnt_succ]
    by_cases h : t = T
    · subst h; simp [hp]
    · have := ih (by omega); omega

theorem mul_cnt (T : Nat) (p : Nat → Bool) (x : Nat) :
    x * cnt T p = sm T (fun t => if p t then x else 0) := by
  unfold cnt; rw [← sm_mul_const]; apply sm_congr; intro t _; cases p t <;> simp

/-- Reindexing a sum over `[0, N)` by an injective partial map from `[0, T)`. -/
theorem sm_reindex (N T : Nat) (y : Nat → Bool) (g : Nat → Nat) (F : Nat → Nat)
    (hg : ∀ t, t < T → y t = true → g t < N)
    (hF : ∀ u, u < N → F u = F u * cnt T (fun t => y t && g t == u)) :
    sm N F = sm T (fun t => if y t then F (g t) else 0) := by
  rw [sm_congr (g := fun u => sm T (fun t => if (y t && g t == u) then F u else 0))]
  · rw [sm_comm]; apply sm_congr; intro t ht
    by_cases hy : y t = true
    · rw [sm_congr (g := fun u => if g t == u then F (g t) else 0)]
      · rw [sm_single N (g t) _ (hg t ht hy)]; simp [hy]
      · intro u _
        by_cases e : g t = u
        · subst e; simp [hy]
        · have : (g t == u) = false := by simp [e]
          simp [this]
    · have hy' : y t = false := by cases h : y t <;> simp_all
      simp only [hy', Bool.false_and]; simp [sm_zero_fun]
  · intro u hu; show F u = _; conv => lhs; rw [hF u hu]
    rw [mul_cnt]

theorem cnt_mono {n n' : Nat} (p : Nat → Bool) (h : n ≤ n') : cnt n p ≤ cnt n' p := by
  induction n' with
  | zero => have : n = 0 := by omega
            subst this; simp
  | succ n' ih =>
    by_cases e : n = n' + 1
    · subst e; exact Nat.le_refl _
    · rw [cnt_succ]; have := ih (by omega); omega

theorem cnt_le_of {n : Nat} {p q : Nat → Bool} (h : ∀ t, t < n → p t = true → q t = true) :
    cnt n p ≤ cnt n q := by
  unfold cnt; apply sm_le_mono; intro t ht
  cases hp : p t
  · simp
  · simp [h t ht hp]

theorem cnt_le_n (n : Nat) (p : Nat → Bool) : cnt n p ≤ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [cnt_succ]; split <;> omega

end Dim8Lift
