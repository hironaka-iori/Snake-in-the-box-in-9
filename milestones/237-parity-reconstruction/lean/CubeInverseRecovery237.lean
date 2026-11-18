import CubeInverseReconstruct237

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

instance vertexDecEq : (n : Nat) → DecidableEq (Vertex n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 =>
    letI := vertexDecEq n
    inferInstanceAs (DecidableEq (Bool × Vertex n))

theorem inner_zero_r (n : Nat) (f : Vertex n → Int) :
    inner n f (fun _ => 0) = 0 := by
  induction n with
  | zero => simp [inner]
  | succ n ih => simp [inner, ih]

theorem inner_mass (n : Nat) (a : Vertex n) (c : Int) (f : Vertex n → Int) :
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

theorem anti_weight (n : Nat) (a b : Vertex n) :
    weight n (translate n (antipode n a) b) + weight n (translate n a b) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    have h := ih a b
    cases s <;> cases t <;> simp [antipode, translate, weight] <;> omega

theorem shift_comm (n : Nat) (a b : Vertex n) :
    translate n a b = translate n b a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨s, a⟩
    rcases b with ⟨t, b⟩
    cases s <;> cases t <;> simp [translate, ih a b]

theorem shift_weight_zero (n : Nat) (a b : Vertex n) :
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

def kernel (a b : Vertex 9) := coefficient (weight 9 (translate 9 a b))

theorem anti_diag (a : Vertex 9) : kernel (antipode 9 a) a = 128 := by
  have h := anti_weight 9 a a
  rw [(shift_weight_zero 9 a a).mpr rfl, Nat.add_zero] at h
  simp [kernel, h, coefficient]

theorem anti_symm (a b : Vertex 9) :
    kernel (antipode 9 a) b = kernel (antipode 9 b) a := by
  have h := anti_weight 9 a b
  have g := anti_weight 9 b a
  rw [shift_comm 9 b a] at g
  unfold kernel
  congr 1
  omega

theorem anti_off (a b : Vertex 9) (h : a ≠ b) :
    kernel (antipode 9 a) b ∈ ([0,35,-10,8,-16] : List Int) := by
  have h1 := anti_weight 9 a b
  have h2 := mt (shift_weight_zero 9 a b).mp h
  have lt : weight 9 (translate 9 (antipode 9 a) b) < 9 := by omega
  unfold kernel
  generalize he : weight 9 (translate 9 (antipode 9 a) b) = k at *
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => decide
  | k + 9 => omega

theorem flip_bound (n : Nat) (z : Vertex n → Int)
    (hz : ∀ x, -1 ≤ z x ∧ z x ≤ 1) (a : Vertex n) :
    -(n : Int) ≤ flipSum n z a ∧ flipSum n z a ≤ (n : Int) := by
  induction n with
  | zero => simp [flipSum]
  | succ n ih =>
    rcases a with ⟨b, a⟩
    have h := ih (fun y => z (b, y)) (fun y => hz (b, y)) a
    have h' := hz (!b, a)
    simp only [flipSum] <;> omega


#print axioms anti_off
#print axioms flip_bound

end CubeInverse
