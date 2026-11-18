import PartialDeficit237

set_option Elab.async false

namespace Cut237
open ContractedDegrees237 PartialDeficit237 LayerJoining

def bit (b : Bool) : Nat := if b then 1 else 0

noncomputable def edgeIndicator (G : Nat → Nat → Prop) (t : Nat → Bool)
    (i j : Nat) : Nat := by
  classical
  exact if G i j ∧ t (j+1) = false then 1 else 0

/-- Counts partners in the complement of T once per distinct target.
S and T need not be disjoint. -/
noncomputable def cutRow (G : Nat → Nat → Prop) (s t : Nat → Bool)
    (k i : Nat) : Nat :=
  if s i then total (k+1) (edgeIndicator G t i) else 0

private theorem one_entry (f : Nat → Nat) {a n : Nat} (ha : a < n) :
    f a ≤ total n f := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases eq : a = n
      · subst a
        simp [total]
      · have q := ih (by omega)
        simp only [total]
        omega

private theorem two_entries (f : Nat → Nat) {a b n : Nat}
    (ha : a < n) (hb : b < n) (distinct : a ≠ b) :
    f a + f b ≤ total n f := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [total]
      by_cases ea : a = n
      · subst a
        have q := one_entry f (show b < n by omega)
        omega
      by_cases eb : b = n
      · subst b
        have q := one_entry f (show a < n by omega)
        omega
      have q := ih (by omega) (by omega)
      omega

private theorem row_bound {G : Nat → Nat → Prop} {k : Nat}
    (sym : ∀ {a b}, G a b → G b a) (steps : ∀ i, i < k → G i (i+1))
    (s t : Nat → Bool) (left : t 0 = true) (right : t (k+2) = true)
    (i : Nat) (hi : i ≤ k) :
    2 * bit (s i) ≤ (bit (t i) + bit (t (i+2))) + cutRow G s t k i := by
  classical
  by_cases si : s i = true
  · have prevEntry (hp : t i = false) : edgeIndicator G t i (i-1) = 1 := by
      have nz : i ≠ 0 := by
        intro eq
        rw [eq, left] at hp
        contradiction
      have prev := steps (i-1) (by omega)
      have back : i-1+1 = i := by omega
      have edge : G i (i-1) := sym (by simpa only [back] using prev)
      simp [edgeIndicator, edge, back, hp]
    have afterEntry (hs : t (i+2) = false) :
        i < k ∧ edgeIndicator G t i (i+1) = 1 := by
      have ne : i ≠ k := by
        intro eq
        rw [eq, right] at hs
        contradiction
      have h : i < k := by omega
      exact ⟨h, by simp [edgeIndicator, steps i h, hs]⟩
    cases hp : t i <;> cases hs : t (i+2)
    · obtain ⟨h, succValue⟩ := afterEntry hs
      have bound := two_entries (edgeIndicator G t i)
        (show i-1 < k+1 by omega) (show i+1 < k+1 by omega) (by omega)
      rw [prevEntry hp, succValue] at bound
      simpa [bit, cutRow, si] using bound
    · have bound := one_entry (edgeIndicator G t i) (show i-1 < k+1 by omega)
      rw [prevEntry hp] at bound
      simp [bit, cutRow, si]
      omega
    · obtain ⟨h, succValue⟩ := afterEntry hs
      have bound := one_entry (edgeIndicator G t i) (show i+1 < k+1 by omega)
      rw [succValue] at bound
      simp [bit, cutRow, si]
      omega
    · simp [bit, cutRow, si]
  · simp [bit, cutRow, si]

private theorem sum_bounds {n : Nat} {f g h : Nat → Nat}
    (bounds : ∀ i, i < n → 2 * f i ≤ g i + h i) :
    2 * total n f ≤ total n g + total n h := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
      have p := ih (fun i hi => bounds i (by omega))
      have q := bounds n (by omega)
      simp only [total]
      omega

/-- For a contracted Hamiltonian order on positions zero to k, double
the S population is bounded by twice the T population, two endpoints,
and the directed count of simple edges from S to its targets outside T.
The flags t 0 and t (k+2) represent the missing boundary positions.
Only flags 1 through k+1 enter the population of T. -/
theorem ordered_cut_bound {G : Nat → Nat → Prop} {k : Nat}
    (sym : ∀ {a b}, G a b → G b a) (steps : ∀ i, i < k → G i (i+1))
    (s t : Nat → Bool) (left : t 0 = true) (right : t (k+2) = true) :
    2 * total (k+1) (fun i => bit (s i)) ≤
      2 * total (k+1) (fun i => bit (t (i+1))) + 2 + total (k+1) (cutRow G s t k) := by
  have rows := sum_bounds (n := k+1)
    (f := fun i => bit (s i)) (g := fun i => bit (t i) + bit (t (i+2)))
    (h := cutRow G s t k) (by intro i hi; exact row_bound sym steps s t left right i (by omega))
  have shifted := shifted_neighbours (k+1) (fun i => bit (t i))
  change total (k+1) (fun i => bit (t i) + bit (t (i+2))) +
    bit (t 1) + bit (t (k+1)) =
    2 * total (k+1) (fun i => bit (t (i+1))) + bit (t 0) + bit (t (k+2)) at shifted
  rw [left, right] at shifted
  change _ + _ + _ = _ + 1 + 1 at shifted
  omega

theorem induced_path_cut_bound {V : Type} {R : V → V → Prop} {k : Nat}
    (p : InducedPath V R (2*k)) (sym : ∀ v w, R v w → R w v)
    (s t : Nat → Bool) (left : t 0 = true) (right : t (k+2) = true) :
    2 * total (k+1) (fun i => bit (s i)) ≤
      2 * total (k+1) (fun i => bit (t (i+1))) + 2 + total (k+1) (cutRow (Partner p) s t k) :=
  ordered_cut_bound partner_symmetric (consecutive_partners p sym) s t left right

#print axioms ordered_cut_bound
#print axioms induced_path_cut_bound

end Cut237
