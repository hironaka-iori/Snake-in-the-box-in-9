/-
Transport and sequence consequence for the (L=7, k=5) automaton, lambda = 7/2.
Core Lean only.  Mirrors `WindowAutomatonLemmas` / `WindowAutomatonSequence`
with eight-direction windows and four previous counts.
-/
import WindowAutomaton5Table
import WindowAutomatonSequence

namespace Snake9.WindowAutomaton

theorem wforb5_canon_drop (ds syms : List Nat) (n : Nat) :
    wforb5 ((canon ds).drop n) syms = wforb5 (ds.drop n) syms := by
  unfold wforb5 wforb5a
  rw [canon_canon_drop, canon_canon_drop_reverse]

theorem pot5_canon_drop (ds t : List Nat) (n : Nat) : pot5 ((canon ds).drop n) t = pot5 (ds.drop n) t := by
  unfold pot5
  rw [canon_canon_drop]

theorem pot5_canon_take (ds t : List Nat) (n : Nat) : pot5 ((canon ds).take n) t = pot5 (ds.take n) t := by
  unfold pot5
  rw [canon_canon_take]

/-- The step inequality for an arbitrary eight-direction window. -/
theorem step5_raw (x : List Nat) (hx : x.length = 8) (t1 t2 t3 t4 s : Nat)
    (h1 : 1 ≤ t1) (h2 : 1 ≤ t2) (h3 : 1 ≤ t3) (h4 : 1 ≤ t4) (hs : 1 ≤ s)
    (hind : inducedPattern x = true)
    (hw2 : wforb5 (x.drop 5) [sym t4, sym s] = false)
    (hw3 : wforb5 (x.drop 4) [sym t3, sym t4, sym s] = false)
    (hw4 : wforb5 (x.drop 3) [sym t2, sym t3, sym t4, sym s] = false)
    (hw5 : wforb5 (x.drop 2) [sym t1, sym t2, sym t3, sym t4, sym s] = false) :
    7 + pot5 (x.drop 1) [sym t2, sym t3, sym t4, sym s] ≤
      2 * sym s + pot5 (x.take 7) [sym t1, sym t2, sym t3, sym t4] := by
  have hc := check5_of_rgs (canon x) (by rw [length_canon, hx]) (canon_isRGS x)
  unfold check5 at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hc
    (sym t1) (sym_ge_one _ h1) (sym_le_six _)) (sym t2) (sym_ge_one _ h2) (sym_le_six _))
    (sym t3) (sym_ge_one _ h3) (sym_le_six _)) (sym t4) (sym_ge_one _ h4) (sym_le_six _))
    (sym s) (sym_ge_one _ hs) (sym_le_six _)
  rw [wforb5_canon_drop, wforb5_canon_drop, wforb5_canon_drop, wforb5_canon_drop, hw2, hw3, hw4, hw5,
    pot5_canon_drop, pot5_canon_take] at h
  simpa using h

def win8 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]

def hist7 (d : Nat → Nat) (i : Nat) : List Nat :=
  [d i, d (i+1), d (i+2), d (i+3), d (i+4), d (i+5), d (i+6)]

def syms4 (a : Nat → Nat) (i : Nat) : List Nat :=
  [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6))]

/-- Potential of the state after centre `i+6`. -/
def Ψ (d a : Nat → Nat) (i : Nat) : Nat := pot5 (hist7 d i) (syms4 a i)

theorem Ψ_le (d a : Nat → Nat) (i : Nat) : Ψ d a i ≤ 15 := pot5_le _ _

theorem step5 (d a : Nat → Nat) (i : Nat)
    (h3 : 1 ≤ a (i+3)) (h4 : 1 ≤ a (i+4)) (h5 : 1 ≤ a (i+5)) (h6 : 1 ≤ a (i+6)) (h7 : 1 ≤ a (i+7))
    (hind : inducedPattern (win8 d i) = true)
    (hw2 : wforb5 [d (i+5), d (i+6), d (i+7)] [sym (a (i+6)), sym (a (i+7))] = false)
    (hw3 : wforb5 [d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw4 : wforb5 [d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false)
    (hw5 : wforb5 [d (i+2), d (i+3), d (i+4), d (i+5), d (i+6), d (i+7)]
      [sym (a (i+3)), sym (a (i+4)), sym (a (i+5)), sym (a (i+6)), sym (a (i+7))] = false) :
    7 + Ψ d a (i+1) ≤ 2 * sym (a (i+7)) + Ψ d a i := by
  have h := step5_raw (win8 d i) rfl (a (i+3)) (a (i+4)) (a (i+5)) (a (i+6)) (a (i+7))
    h3 h4 h5 h6 h7 hind hw2 hw3 hw4 hw5
  exact h

/-- `S5 a n = Σ_{t<n} sym (a (t+7))`. -/
def S5 (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => S5 a n + sym (a (n+7))

theorem invariant5 (d a : Nat → Nat) (m : Nat)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8 d i) = true)
    (hw2 : ∀ j, j + 3 ≤ m → wforb5 [d j, d (j+1), d (j+2)] [sym (a (j+1)), sym (a (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforb5 [d j, d (j+1), d (j+2), d (j+3)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforb5 [d j, d (j+1), d (j+2), d (j+3), d (j+4)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforb5 [d j, d (j+1), d (j+2), d (j+3), d (j+4), d (j+5)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5))] = false) :
    ∀ n, n + 7 ≤ m → 7 * n + Ψ d a n ≤ 2 * S5 a n + Ψ d a 0
  | 0, _ => by simp [S5]
  | n + 1, hn => by
    have ih := invariant5 d a m hpos hind hw2 hw3 hw4 hw5 n (by omega)
    have hs := step5 d a n (hpos (n+3) (by omega) (by omega)) (hpos (n+4) (by omega) (by omega))
      (hpos (n+5) (by omega) (by omega)) (hpos (n+6) (by omega) (by omega))
      (hpos (n+7) (by omega) (by omega)) (hind n (by omega)) (hw2 (n+5) (by omega))
      (hw3 (n+4) (by omega)) (hw4 (n+3) (by omega)) (hw5 (n+2) (by omega))
    simp only [S5]
    omega

theorem sumA_ge5 (a : Nat → Nat) (m : Nat) (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j) :
    ∀ n, n + 7 ≤ m → 6 + S5 a n ≤ sumA a (n + 6)
  | 0, h => by
    simp only [S5, sumA, Nat.zero_add, Nat.reduceAdd]
    have := hpos 1 (by omega) (by omega)
    have := hpos 2 (by omega) (by omega)
    have := hpos 3 (by omega) (by omega)
    have := hpos 4 (by omega) (by omega)
    have := hpos 5 (by omega) (by omega)
    have := hpos 6 (by omega) (by omega)
    omega
  | n + 1, h => by
    have ih := sumA_ge5 a m hpos n (by omega)
    have := sym_le (a (n+7))
    show 6 + (S5 a n + sym (a (n+7))) ≤ sumA a (n+6) + a (n+6+1)
    have he2 : n + 6 + 1 = n + 7 := by omega
    rw [he2]
    omega

/-- Internal counts of an `m`-edge path under the five-centre window exclusions. -/
theorem total_bound5 (d a : Nat → Nat) (m : Nat) (hm : 7 ≤ m)
    (hpos : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ a j)
    (hind : ∀ i, i + 8 ≤ m → inducedPattern (win8 d i) = true)
    (hw2 : ∀ j, j + 3 ≤ m → wforb5 [d j, d (j+1), d (j+2)] [sym (a (j+1)), sym (a (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforb5 [d j, d (j+1), d (j+2), d (j+3)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforb5 [d j, d (j+1), d (j+2), d (j+3), d (j+4)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforb5 [d j, d (j+1), d (j+2), d (j+3), d (j+4), d (j+5)]
      [sym (a (j+1)), sym (a (j+2)), sym (a (j+3)), sym (a (j+4)), sym (a (j+5))] = false) :
    7 * m ≤ 2 * sumA a (m - 1) + 52 := by
  have hinv := invariant5 d a m hpos hind hw2 hw3 hw4 hw5 (m - 7) (by omega)
  have hsum := sumA_ge5 a m hpos (m - 7) (by omega)
  have h0 := Ψ_le d a 0
  have he : m - 7 + 6 = m - 1 := by omega
  rw [he] at hsum
  omega

end Snake9.WindowAutomaton

#print axioms Snake9.WindowAutomaton.total_bound5
