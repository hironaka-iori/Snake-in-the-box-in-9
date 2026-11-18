import Std

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

/-- An n-bit vertex, with the first bit separated from the remaining bits. -/
def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Vertex n

def flipSum : (n : Nat) → (Vertex n → Int) → Vertex n → Int
  | 0, _, _ => 0
  | n + 1, f, (b, x) =>
    f (!b, x) + flipSum n (fun y => f (b, y)) x

def inner : (n : Nat) → (Vertex n → Int) → (Vertex n → Int) → Int
  | 0, f, g => f () * g ()
  | n + 1, f, g =>
    inner n (fun x => f (false, x)) (fun x => g (false, x)) +
    inner n (fun x => f (true, x)) (fun x => g (true, x))

private theorem inner_add_l (n : Nat) (f g h : Vertex n → Int) :
    inner n (fun x => f x + g x) h = inner n f h + inner n g h := by
  induction n with
  | zero => exact Int.add_mul _ _ _
  | succ n ih => simp only [inner, ih]; omega

private theorem inner_add_r (n : Nat) (f g h : Vertex n → Int) :
    inner n f (fun x => g x + h x) = inner n f g + inner n f h := by
  induction n with
  | zero => exact Int.mul_add _ _ _
  | succ n ih => simp only [inner, ih]; omega

private theorem self_adjoint (n : Nat) (f g : Vertex n → Int) :
    inner n f (flipSum n g) = inner n (flipSum n f) g := by
  induction n with
  | zero => simp [inner, flipSum]
  | succ n ih =>
    simp only [inner, flipSum, Bool.not_false, Bool.not_true, inner_add_l,
      inner_add_r, ih]
    omega

def translate : (n : Nat) → Vertex n → Vertex n → Vertex n
  | 0, _, _ => ()
  | n + 1, (b, x), (c, y) =>
    (if b then !c else c, translate n x y)

private theorem flip_translate (n : Nat) (f : Vertex n → Int) (a x : Vertex n) :
    flipSum n (fun y => f (translate n a y)) x = flipSum n f (translate n a x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    rcases x with ⟨c, x⟩
    cases b <;> cases c <;> simp [translate, flipSum]
    · exact ih (fun y => f (false, y)) a x
    · exact ih (fun y => f (true, y)) a x
    · exact ih (fun y => f (true, y)) a x
    · exact ih (fun y => f (false, y)) a x

def weight : (n : Nat) → Vertex n → Nat
  | 0, _ => 0
  | n + 1, (b, x) => (if b then 1 else 0) + weight n x

def coefficient : Nat → Int
  | 1 => 35
  | 3 => -10
  | 5 => 8
  | 7 => -16
  | 9 => 128
  | _ => 0

def spike : (n : Nat) → Vertex n → Int
  | 0, _ => 315
  | n + 1, (b, x) => if b then 0 else spike n x

private theorem inner_zero_l (n : Nat) (f : Vertex n → Int) :
    inner n (fun _ => 0) f = 0 := by
  induction n with
  | zero => simp [inner]
  | succ n ih => simp [inner, ih]

private theorem inner_spike (n : Nat) (a : Vertex n) (f : Vertex n → Int) :
    inner n (fun x => spike n (translate n a x)) f = 315 * f a := by
  induction n with
  | zero => cases a; rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    cases b <;> simp [inner, translate, spike, ih, inner_zero_l]

private def every : (n : Nat) → (Vertex n → Bool) → Bool
  | 0, f => f ()
  | n + 1, f =>
    every n (fun x => f (false, x)) && every n (fun x => f (true, x))

private theorem of_every (n : Nat) (p : Vertex n → Bool) (h : every n p = true)
    (x : Vertex n) : p x = true := by
  induction n with
  | zero => cases x; exact h
  | succ n ih =>
    rcases x with ⟨b, x⟩
    obtain ⟨l, r⟩ := Bool.and_eq_true_iff.mp h
    cases b
    · exact ih _ l x
    · exact ih _ r x

private theorem kernel_origin (x : Vertex 9) :
    flipSum 9 (fun y => coefficient (weight 9 y)) x = spike 9 x := by
  have h : every 9 (fun z =>
      flipSum 9 (fun y => coefficient (weight 9 y)) z == spike 9 z) = true := by decide
  exact beq_iff_eq.mp (of_every _ _ h x)

/-- Exact inverse for the ordinary one-coordinate-flip neighbour sum on Q9.
The sum in the left hand side is over all 512 bit vectors. -/
theorem reconstruct (z : Vertex 9 → Int) (a : Vertex 9) :
    inner 9 (fun x => coefficient (weight 9 (translate 9 a x))) (flipSum 9 z)
      = 315 * z a := by
  rw [self_adjoint]
  have h : flipSum 9 (fun x => coefficient (weight 9 (translate 9 a x))) =
      fun x => spike 9 (translate 9 a x) := by
    funext x
    exact (flip_translate 9 (fun y => coefficient (weight 9 y)) a x).trans
      (kernel_origin _)
  rw [h, inner_spike]

theorem neighbour_sum_injective (f g : Vertex 9 → Int)
    (h : flipSum 9 f = flipSum 9 g) : f = g := by
  funext a
  have hf := reconstruct f a
  have hg := reconstruct g a
  rw [h] at hf
  omega

#print axioms reconstruct
#print axioms neighbour_sum_injective

instance vertexDecEq : (n : Nat) → DecidableEq (Vertex n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 =>
    letI := vertexDecEq n
    inferInstanceAs (DecidableEq (Bool × Vertex n))

private theorem inner_zero_r (n : Nat) (f : Vertex n → Int) :
    inner n f (fun _ => 0) = 0 := by
  induction n with
  | zero => simp [inner]
  | succ n ih => simp [inner, ih]

private theorem inner_mass (n : Nat) (a : Vertex n) (c : Int) (f : Vertex n → Int) :
    inner n f (fun x => if x = a then c else 0) = f a * c := by
  induction n with
  | zero => cases a; simp [inner]
  | succ n ih =>
    rcases a with ⟨b, a⟩
    have diag (d : Bool) :
        (fun x : Vertex n => if ((d,x) : Vertex (n+1)) = (d,a) then c else 0) =
        (fun x => if x = a then c else 0) := by
      funext x
      by_cases h : x = a
      · subst x; simp
      · exact (if_neg (fun e => h (congrArg Prod.snd e))).trans (if_neg h).symm
    have off (d e : Bool) (h : d ≠ e) :
        (fun x : Vertex n => if ((d,x) : Vertex (n+1)) = (e,a) then c else 0) =
        (fun _ => 0) := by
      funext x
      exact if_neg (fun eq => h (congrArg Prod.fst eq))
    cases b
    · simp only [inner, diag false, off true false (by decide), inner_zero_r,
        Int.add_zero, ih]
    · simp only [inner, diag true, off false true (by decide), inner_zero_r,
        Int.zero_add, ih]

def antipode : (n : Nat) → Vertex n → Vertex n
  | 0, _ => ()
  | n + 1, (b, x) => (!b, antipode n x)

private theorem anti_weight (n : Nat) (a b : Vertex n) :
    weight n (translate n (antipode n a) b) + weight n (translate n a b) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    have h := ih a b
    cases s <;> cases t <;> simp [antipode, translate, weight] <;> omega

private theorem shift_comm (n : Nat) (a b : Vertex n) :
    translate n a b = translate n b a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    cases s <;> cases t <;> simp [translate, ih a b]

private theorem shift_weight_zero (n : Nat) (a b : Vertex n) :
    weight n (translate n a b) = 0 ↔ a = b := by
  induction n with
  | zero => cases a; cases b; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    cases s <;> cases t <;> simp [translate, weight, ih, Nat.succ_add]
    · exact ⟨fun h => congrArg (fun y : Vertex n => ((false,y) : Vertex (n+1))) h,
        fun h => congrArg Prod.snd h⟩
    · exact fun h => Bool.noConfusion (congrArg Prod.fst h)
    · exact fun h => Bool.noConfusion (congrArg Prod.fst h)
    · exact ⟨fun h => congrArg (fun y : Vertex n => ((true,y) : Vertex (n+1))) h,
        fun h => congrArg Prod.snd h⟩

private def kernel (a b : Vertex 9) := coefficient (weight 9 (translate 9 a b))

private theorem anti_diag (a : Vertex 9) : kernel (antipode 9 a) a = 128 := by
  have h := anti_weight 9 a a
  rw [(shift_weight_zero 9 a a).mpr rfl, Nat.add_zero] at h
  simp [kernel, h, coefficient]

private theorem anti_symm (a b : Vertex 9) :
    kernel (antipode 9 a) b = kernel (antipode 9 b) a := by
  have h := anti_weight 9 a b
  have g := anti_weight 9 b a
  rw [shift_comm 9 b a] at g
  unfold kernel
  congr 1
  omega

private theorem anti_off (a b : Vertex 9) (h : a ≠ b) :
    kernel (antipode 9 a) b ∈ ([0,35,-10,8,-16] : List Int) := by
  have h1 := anti_weight 9 a b
  have h2 := mt (shift_weight_zero 9 a b).mp h
  have lt : weight 9 (translate 9 (antipode 9 a) b) < 9 := by omega
  unfold kernel
  generalize he : weight 9 (translate 9 (antipode 9 a) b) = k at *
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => decide
  | k + 9 => omega

private theorem flip_bound (n : Nat) (z : Vertex n → Int)
    (hz : ∀ x, -1 ≤ z x ∧ z x ≤ 1) (a : Vertex n) :
    -(n : Int) ≤ flipSum n z a ∧ flipSum n z a ≤ (n : Int) := by
  induction n with
  | zero => simp [flipSum]
  | succ n ih =>
    rcases a with ⟨b, a⟩
    have h := ih (fun y => z (b, y)) (fun y => hz (b, y)) a
    have h' := hz (!b, a)
    simp only [flipSum] <;> omega

private theorem two_coeff (c x y s t : Int) (hc : c ∈ ([0,35,-10,8,-16] : List Int))
    (hx : -9 ≤ x ∧ x ≤ 9) (hy : -9 ≤ y ∧ y ≤ 9)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (h1 : 128*x + c*y = 315*s) (h2 : c*x + 128*y = 315*t) :
    x = 0 ∧ y = 0 := by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    have s_cases : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  all_goals rcases s_cases with rfl | rfl | rfl <;>
    have t_cases : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  all_goals rcases t_cases with rfl | rfl | rfl <;> omega

/-- A signed difference of binary selections cannot have its neighbour-sum
profile supported on at most two arbitrary vertices. -/
theorem two_erasures (z : Vertex 9 → Int) (hz : ∀ x, -1 ≤ z x ∧ z x ≤ 1)
    (a b : Vertex 9) (hab : a ≠ b)
    (away : ∀ x, x ≠ a → x ≠ b → flipSum 9 z x = 0) :
    z = fun _ => 0 := by
  let v := flipSum 9 z
  have obs : flipSum 9 z = fun x =>
      (if x = a then v a else 0) + (if x = b then v b else 0) := by
    funext x
    by_cases ha : x = a
    · subst x; simp [hab, v]
    by_cases hb : x = b
    · subst x; simp [Ne.symm hab, v]
    simp [ha, hb, away x ha hb]
  have row (p : Vertex 9) : kernel p a * v a + kernel p b * v b = 315 * z p := by
    have h := reconstruct z p
    rw [obs, inner_add_r, inner_mass, inner_mass] at h
    exact h
  have r := row (antipode 9 a)
  have s := row (antipode 9 b)
  rw [anti_diag] at r s
  rw [anti_symm b a] at s
  obtain ⟨za,zb⟩ := two_coeff _ _ _ _ _ (anti_off a b hab)
    (flip_bound 9 z hz a) (flip_bound 9 z hz b) (hz _) (hz _) r s
  funext p
  have h := row p
  change v a = 0 at za
  change v b = 0 at zb
  rw [za,zb,Int.mul_zero,Int.mul_zero,Int.add_zero] at h
  omega

#print axioms two_erasures

def indicator (f : Vertex 9 → Bool) (x : Vertex 9) : Int := if f x then 1 else 0

private theorem flip_sub (n : Nat) (f g : Vertex n → Int) (a : Vertex n) :
    flipSum n (fun x => f x - g x) a = flipSum n f a - flipSum n g a := by
  induction n with
  | zero => simp [flipSum]
  | succ n ih =>
    rcases a with ⟨b,a⟩
    simp only [flipSum]
    rw [ih (fun y => f (b,y)) (fun y => g (b,y))]
    omega

theorem determine_selection (f g : Vertex 9 → Bool) (a b : Vertex 9) (hab : a ≠ b)
    (agree : ∀ x, x ≠ a → x ≠ b →
      flipSum 9 (indicator f) x = flipSum 9 (indicator g) x) : f = g := by
  let z := fun x => indicator f x - indicator g x
  have bounded (x) : -1 ≤ z x ∧ z x ≤ 1 := by
    cases hf : f x <;> cases hg : g x <;> simp [z,indicator,hf,hg]
  have away (x) (ha : x ≠ a) (hb : x ≠ b) : flipSum 9 z x = 0 := by
    unfold z
    rw [flip_sub, agree x ha hb, Int.sub_self]
  have h := two_erasures z bounded a b hab away
  funext x
  have zero := congrFun h x
  cases hf : f x <;> cases hg : g x <;> simp [z,indicator,hf,hg] at zero ⊢

#print axioms determine_selection

end CubeInverse
