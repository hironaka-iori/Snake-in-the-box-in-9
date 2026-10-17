/-
Sequence potential for the conditional 242-edge bound.

This module uses only core Lean. It proves an abstract statement about
natural-number sequences; it says nothing about snakes by itself. The
window exclusions it assumes are solver-certified (DRAT) observations
recorded in `milestones/10-window-aggregate/`, not Lean theorems.
-/
namespace Snake9.WindowAggregate

/-- Values above six are lumped together; every assumed pattern uses values at most six. -/
def clamp (a : Nat) : Nat := if a ≤ 6 then a else 7

/-- Count-one neighbours have count at least four (proved in `Aggregate245Conditional`). -/
def PairOK (x y : Nat) : Prop := (x = 1 → 4 ≤ y) ∧ (y = 1 → 4 ≤ x)

/-- The excluded internal triples: 222 (proved), and the certified 223, 224, 232, 323,
41c, c14 (4 ≤ c ≤ 6), with reversals. -/
def Excluded (x y z : Nat) : Prop :=
  (x = 2 ∧ y = 2 ∧ 2 ≤ z ∧ z ≤ 4) ∨ (z = 2 ∧ y = 2 ∧ 2 ≤ x ∧ x ≤ 4) ∨
  (x = 2 ∧ y = 3 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 3) ∨
  (x = 4 ∧ y = 1 ∧ 4 ≤ z ∧ z ≤ 6) ∨ (z = 4 ∧ y = 1 ∧ 4 ≤ x ∧ x ≤ 6)

/-- The excluded triples other than the proved 222: these are the window exclusions that are
DRAT-certified for the local ball model but not yet Lean-checked. -/
def Certified (x y z : Nat) : Prop := Excluded x y z ∧ ¬(x = 2 ∧ y = 2 ∧ z = 2)

/-- Potential on clamped pairs (the longest-path potential for weight 14 - 5z). -/
def potC : Nat → Nat → Nat
  | 1, 4 => 3 | 2, 2 => 8 | 2, 3 => 6 | 2, 4 => 3 | 3, 2 => 9 | 3, 3 => 5
  | 4, 1 => 12 | 4, 2 => 7 | 4, 3 => 2 | 5, 1 => 9 | 5, 2 => 4 | 6, 1 => 9
  | 6, 2 => 4 | 7, 1 => 9 | 7, 2 => 4 | _, _ => 0

def pot (a b : Nat) : Nat := potC (clamp a) (clamp b)

/-! Bounded Boolean checks, evaluated by the kernel. -/

def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

theorem allBelow_spec : ∀ n (p : Nat → Bool), allBelow n p = true → ∀ a, a < n → p a = true
  | 0, _, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | n + 1, p, h, a, ha => by
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases hn : a = n
    · subst hn; exact h.2
    · exact allBelow_spec n p h.1 a (by omega)

def pairB (x y : Nat) : Bool := (x != 1 || decide (4 ≤ y)) && (y != 1 || decide (4 ≤ x))

def exclB (x y z : Nat) : Bool :=
  decide ((x = 2 ∧ y = 2 ∧ 2 ≤ z ∧ z ≤ 4) ∨ (z = 2 ∧ y = 2 ∧ 2 ≤ x ∧ x ≤ 4) ∨
  (x = 2 ∧ y = 3 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 3) ∨
  (x = 4 ∧ y = 1 ∧ 4 ≤ z ∧ z ≤ 6) ∨ (z = 4 ∧ y = 1 ∧ 4 ≤ x ∧ x ≤ 6))

def stepB (a b c : Nat) : Bool :=
  !(decide (1 ≤ a) && decide (1 ≤ b) && decide (1 ≤ c) && pairB a b && pairB b c && !exclB a b c)
    || decide (14 + potC a b ≤ 5 * c + potC b c)

def baseB (a b : Nat) : Bool :=
  !(decide (1 ≤ a) && decide (1 ≤ b) && pairB a b) || decide (28 ≤ 5 * a + 5 * b + potC a b)

theorem step_table : allBelow 8 (fun a => allBelow 8 (fun b => allBelow 8 (fun c => stepB a b c))) = true := by
  decide

theorem base_table : allBelow 8 (fun a => allBelow 8 (fun b => baseB a b)) = true := by
  decide

theorem pot_table : allBelow 8 (fun a => allBelow 8 (fun b => decide (potC a b ≤ 12))) = true := by
  decide

theorem clamp_lt (a : Nat) : clamp a < 8 := by unfold clamp; split <;> omega

theorem clamp_cases (a : Nat) : (a ≤ 6 ∧ clamp a = a) ∨ (7 ≤ a ∧ clamp a = 7) := by
  unfold clamp; split <;> omega

theorem pot_le (a b : Nat) : pot a b ≤ 12 := by
  have h := allBelow_spec 8 _ (allBelow_spec 8 _ pot_table (clamp a) (clamp_lt a)) (clamp b) (clamp_lt b)
  simpa [pot] using h

theorem stepB_sound (a b c : Nat) (h : stepB a b c = true) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (h1 : pairB a b = true) (h2 : pairB b c = true) (he : exclB a b c = false) :
    14 + potC a b ≤ 5 * c + potC b c := by
  simpa [stepB, ha, hb, hc, h1, h2, he] using h

theorem pair_clamp (x y : Nat) (h : PairOK x y) : pairB (clamp x) (clamp y) = true := by
  unfold PairOK at h
  unfold pairB
  rcases clamp_cases x with ⟨_, ex⟩ | ⟨_, ex⟩ <;>
  rcases clamp_cases y with ⟨_, ey⟩ | ⟨_, ey⟩ <;>
  rw [ex, ey] <;>
  · simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    omega

theorem excl_clamp (x y z : Nat) (h : ¬Excluded x y z) :
    exclB (clamp x) (clamp y) (clamp z) = false := by
  unfold exclB
  rw [decide_eq_false_iff_not]
  intro hh
  apply h
  unfold Excluded
  rcases clamp_cases x with ⟨_, ex⟩ | ⟨_, ex⟩ <;>
  rcases clamp_cases y with ⟨_, ey⟩ | ⟨_, ey⟩ <;>
  rcases clamp_cases z with ⟨_, ez⟩ | ⟨_, ez⟩ <;>
  rw [ex, ey, ez] at hh <;>
  rcases hh with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
  first
    | omega
    | exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
    | exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, by omega⟩))))

theorem clamp_ge_one (a : Nat) (h : 1 ≤ a) : 1 ≤ clamp a := by
  rcases clamp_cases a with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

theorem le_clamp_mul (z : Nat) : 5 * clamp z ≤ 5 * z := by
  rcases clamp_cases z with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

theorem step (x y z : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hxy : PairOK x y) (hyz : PairOK y z) (hex : ¬Excluded x y z) :
    14 + pot x y ≤ 5 * z + pot y z := by
  have hc := allBelow_spec 8 _ (allBelow_spec 8 _ (allBelow_spec 8 _ step_table
    (clamp x) (clamp_lt x)) (clamp y) (clamp_lt y)) (clamp z) (clamp_lt z)
  have := stepB_sound _ _ _ hc (clamp_ge_one x hx) (clamp_ge_one y hy) (clamp_ge_one z hz)
    (pair_clamp x y hxy) (pair_clamp y z hyz) (excl_clamp x y z hex)
  have := le_clamp_mul z
  unfold pot
  omega

theorem base (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : PairOK a b) :
    28 ≤ 5 * a + 5 * b + pot a b := by
  have hc := allBelow_spec 8 _ (allBelow_spec 8 _ base_table (clamp a) (clamp_lt a)) (clamp b) (clamp_lt b)
  have := pair_clamp a b hab
  have hc' : 28 ≤ 5 * clamp a + 5 * clamp b + potC (clamp a) (clamp b) := by
    simpa [baseB, clamp_ge_one a ha, clamp_ge_one b hb, this] using hc
  have := le_clamp_mul a
  have := le_clamp_mul b
  unfold pot
  omega

/-- Prefix sums without any library dependency. -/
def psum (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => psum h k + h k

theorem prefix_cost (h : Nat → Nat) : ∀ n, 2 ≤ n →
    (∀ j, j < n → 1 ≤ h j) →
    (∀ j, j + 1 < n → PairOK (h j) (h (j + 1))) →
    (∀ j, j + 2 < n → ¬Excluded (h j) (h (j + 1)) (h (j + 2))) →
    14 * n ≤ 5 * psum h n + pot (h (n - 2)) (h (n - 1))
  | 0, hn, _, _, _ => by omega
  | 1, hn, _, _, _ => by omega
  | 2, _, hpos, hpair, _ => by
    have := base (h 0) (h 1) (hpos 0 (by omega)) (hpos 1 (by omega)) (hpair 0 (by omega))
    simp only [psum, show (2 : Nat) - 2 = 0 from rfl, show (2 : Nat) - 1 = 1 from rfl]
    omega
  | k + 3, _, hpos, hpair, hex => by
    have ih := prefix_cost h (k + 2) (by omega) (fun j hj => hpos j (by omega))
      (fun j hj => hpair j (by omega)) (fun j hj => hex j (by omega))
    have hs := step (h k) (h (k + 1)) (h (k + 2)) (hpos _ (by omega)) (hpos _ (by omega))
      (hpos _ (by omega)) (hpair k (by omega)) (hpair (k + 1) (by omega)) (hex k (by omega))
    simp only [psum] at ih ⊢
    simp only [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega] at ih
    simp only [show k + 3 - 2 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega]
    omega

/-- Internal counts average at least 14/5, up to an additive 12. -/
theorem internal_cost (h : Nat → Nat) (n : Nat) (hn : 2 ≤ n)
    (hpos : ∀ j, j < n → 1 ≤ h j)
    (hpair : ∀ j, j + 1 < n → PairOK (h j) (h (j + 1)))
    (hex : ∀ j, j + 2 < n → ¬Excluded (h j) (h (j + 1)) (h (j + 2))) :
    14 * n ≤ 5 * psum h n + 12 := by
  have := prefix_cost h n hn hpos hpair hex
  have := pot_le (h (n - 2)) (h (n - 1))
  omega

/-- Arithmetic of the incidence identity: with internal sum `I` over `m-1` internal
vertices, endpoint counts at least four, and `T + 2*E0 + 35*(m+1) = 9214`, at most
242 edges remain. -/
theorem edges_le_242 (m I e0 e1 E0 : Nat)
    (hI : 14 * (m - 1) ≤ 5 * I + 12) (h0 : 4 ≤ e0) (h1 : 4 ≤ e1)
    (hid : e0 + I + e1 + 2 * E0 + 35 * (m + 1) = 9214) : m ≤ 242 := by
  omega

end Snake9.WindowAggregate

#print axioms Snake9.WindowAggregate.internal_cost
#print axioms Snake9.WindowAggregate.edges_le_242
