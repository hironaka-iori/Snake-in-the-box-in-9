/-
Sequence consequence of the direction-aware automaton.

For a path with `m` edges, read as directions `d 0, …, d (m-1)` and internal
singleton counts `a 1, …, a (m-1)`, the kernel-checked step table yields
`10 m ≤ 3 Σ_{j=1}^{m-1} a j + 60`, provided every seven-direction block is
induced and no certified window pattern occurs.  Core Lean only.
-/
import WindowAutomatonLemmas

namespace Snake9.WindowAutomaton

def win7 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6)]

def hist (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5)]

def syms3 (a : Nat → Nat) (i : Nat) : List Nat :=
  [sym (a (i+3)), sym (a (i+4)), sym (a (i+5))]

/-- Potential of the state after centre `i+5`. -/
def Φ (d a : Nat → Nat) (i : Nat) : Nat := pot (hist d i) (syms3 a i)

theorem Φ_le (d a : Nat → Nat) (i : Nat) : Φ d a i ≤ 15 := pot_le _ _

theorem step (d a : Nat → Nat) (i : Nat)
    (h3 : 1 ≤ a (i+3)) (h4 : 1 ≤ a (i+4)) (h5 : 1 ≤ a (i+5)) (h6 : 1 ≤ a (i+6))
    (hind : inducedPattern (win7 d i) = true)
    (hw2 : wforb [d (i+4), d (i+5), d (i+6)] [sym (a (i+5)), sym (a (i+6))] = false)
    (hw3 : wforb [d (i+3), d (i+4), d (i+5), d (i+6)]
      [sym (a (i+4)), sym (a (i+5)), sym (a (i+6))] = false)
    (hw4 : wforb [d (i+2), d (i+3), d (i+4), d (i+5), d (i+6)]
      [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6))] = false) :
    10 + Φ d a (i+1) ≤ 3 * sym (a (i+6)) + Φ d a i := by
  have h := step_raw (win7 d i) rfl (a (i+3)) (a (i+4)) (a (i+5)) (a (i+6)) h3 h4 h5 h6 hind hw2 hw3 hw4
  exact h

/-- `S a n = Σ_{t<n} sym (a (t+6))`. -/
def S (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S a n + sym (a (n+6))

/-- `sumA a n = Σ_{j=1}^{n} a j`. -/
def sumA (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumA a n + a (n+1)

theorem invariant (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 7 ≤ m → inducedPattern (win7 d i) = true)
    (hw2 : ∀ j, j + 3 ≤ m → wforb [d j, d (j+1), d (j+2)] [sym (a (j+1)), sym (a (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforb [d j, d (j+1), d (j+2), d (j+3)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforb [d j, d (j+1), d (j+2), d (j+3), d (j+4)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4))] = false) :
    ∀ n, n + 6 ≤ m → 10 * n + Φ d a n ≤ 3 * S a n + Φ d a 0
  | 0, _ => by simp [S]
  | n + 1, hn => by
    have ih := invariant d a m hpos hind hw2 hw3 hw4 n (by omega)
    have hs := step d a n (hpos (n+3) (by omega) (by omega)) (hpos (n+4) (by omega) (by omega))
      (hpos (n+5) (by omega) (by omega)) (hpos (n+6) (by omega) (by omega))
      (hind n (by omega)) (hw2 (n+4) (by omega)) (hw3 (n+3) (by omega)) (hw4 (n+2) (by omega))
    simp only [S]
    omega

theorem sumA_ge (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
    ∀ n, n + 6 ≤ m → 5 + S a n ≤ sumA a (n + 5)
  | 0, h => by
    simp only [S, sumA, Nat.zero_add, Nat.reduceAdd]
    have := hpos 1 (by omega) (by omega)
    have := hpos 2 (by omega) (by omega)
    have := hpos 3 (by omega) (by omega)
    have := hpos 4 (by omega) (by omega)
    have := hpos 5 (by omega) (by omega)
    omega
  | n + 1, h => by
    have ih := sumA_ge a m hpos n (by omega)
    have := sym_le (a (n+6))
    show 5 + (S a n + sym (a (n+6))) ≤ sumA a (n+5) + a (n+5+1)
    have he2 : n + 5 + 1 = n + 6 := by omega
    rw [he2]
    omega

/-- Internal counts of an `m`-edge path, under the certified window exclusions. -/
theorem total_bound (d a : Nat → Nat) (m : Nat) (hm : 6 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 7 ≤ m → inducedPattern (win7 d i) = true)
    (hw2 : ∀ j, j + 3 ≤ m → wforb [d j, d (j+1), d (j+2)] [sym (a (j+1)), sym (a (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforb [d j, d (j+1), d (j+2), d (j+3)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforb [d j, d (j+1), d (j+2), d (j+3), d (j+4)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4))] = false) :
    10 * m ≤ 3 * sumA a (m - 1) + 60 := by
  have hinv := invariant d a m hpos hind hw2 hw3 hw4 (m - 6) (by omega)
  have hsum := sumA_ge a m hpos (m - 6) (by omega)
  have h0 := Φ_le d a 0
  have he : m - 6 + 5 = m - 1 := by omega
  rw [he] at hsum
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.total_bound
