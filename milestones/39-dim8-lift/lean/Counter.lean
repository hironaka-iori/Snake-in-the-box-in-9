import LocalWindowModel
/-! Sequential counter (Sinz) for "at most k of the literals xs are true", with its soundness: the
assignment that sets each register `R(i,j)` to "at least j of the first i literals are true"
satisfies every clause when the bound holds.  Literals are DIMACS integers. -/
namespace Dim8Lift.Cnf
open Snake9.LocalWindow

def pos (v : Nat) : Int := Int.ofNat v
def neg (v : Nat) : Int := -Int.ofNat v

theorem litTrue_pos (τ : Nat → Bool) {v : Nat} (hv : 0 < v) : litTrue τ (pos v) = τ v := by
  unfold litTrue pos; simp; omega
theorem litTrue_neg (τ : Nat → Bool) {v : Nat} (hv : 0 < v) : litTrue τ (neg v) = !τ v := by
  unfold litTrue neg; simp; omega

/-- Number of true literals among the first `i` of `xs`. -/
def cl (τ : Nat → Bool) (xs : List Int) (i : Nat) : Nat :=
  ((xs.take i).filter (litTrue τ)).length

/-- Register variable for "at least j of the first i", `1 ≤ i ≤ n`, `1 ≤ j ≤ k`. -/
def reg (base k i j : Nat) : Nat := base + (i - 1) * k + (j - 1)

def negLit (l : Int) : Int := -l

/-- Sinz clauses for `at most k` (k ≥ 1) of `xs`, registers from `base`. -/
def atMost (base k : Nat) (xs : List Int) : List (List Int) :=
  let n := xs.length
  let x := fun i => xs.getD (i - 1) 0
  ([negLit (x 1), pos (reg base k 1 1)] :: (List.range (k - 1)).map (fun j => [neg (reg base k 1 (j + 2))])) ++
  ((List.range (n - 1)).flatMap fun i0 =>
    let i := i0 + 2
    [negLit (x i), pos (reg base k i 1)] :: [neg (reg base k (i - 1) 1), pos (reg base k i 1)] ::
    [negLit (x i), neg (reg base k (i - 1) k)] ::
    ((List.range (k - 1)).flatMap fun j0 =>
      let j := j0 + 2
      [[negLit (x i), neg (reg base k (i - 1) (j - 1)), pos (reg base k i j)],
       [neg (reg base k (i - 1) j), pos (reg base k i j)]]))

end Dim8Lift.Cnf

namespace Dim8Lift.Cnf
open Snake9.LocalWindow

theorem litTrue_negLit (τ : Nat → Bool) {l : Int} (hl : l ≠ 0) : litTrue τ (negLit l) = !litTrue τ l := by
  unfold litTrue negLit
  by_cases h : 0 < l
  · rw [if_neg (by omega), if_pos h]; simp
  · rw [if_pos (by omega), if_neg h]; simp

theorem cl_succ (τ : Nat → Bool) (xs : List Int) {i : Nat} (hi : i < xs.length) :
    cl τ xs (i + 1) = cl τ xs i + (if litTrue τ (xs.getD i 0) then 1 else 0) := by
  unfold cl
  have e : xs.getD i 0 = xs[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp
  rw [List.take_succ, List.filter_append, List.length_append, List.getElem?_eq_getElem hi, e]
  simp only [Option.toList_some]
  cases h : litTrue τ xs[i] <;> simp [List.filter, h]

theorem cl_mono (τ : Nat → Bool) (xs : List Int) {i i' : Nat} (h : i ≤ i') : cl τ xs i ≤ cl τ xs i' := by
  unfold cl
  have : xs.take i = (xs.take i').take i := by rw [List.take_take]; congr 1; omega
  rw [this]
  exact List.Sublist.length_le (List.Sublist.filter _ (List.take_sublist _ _))

theorem cl_zero (τ : Nat → Bool) (xs : List Int) : cl τ xs 0 = 0 := by simp [cl]

theorem atMost_sound (τ : Nat → Bool) (base k : Nat) (xs : List Int) (hk : 1 ≤ k) (hb : 1 ≤ base) (hn : 1 ≤ xs.length)
    (hlits : ∀ l ∈ xs, l ≠ 0)
    (hR : ∀ i j, 1 ≤ i → i ≤ xs.length → 1 ≤ j → j ≤ k → τ (reg base k i j) = decide (j ≤ cl τ xs i))
    (hbound : cl τ xs xs.length ≤ k) :
    ∀ c ∈ atMost base k xs, clauseTrue τ c = true := by
  have hx : ∀ i, 1 ≤ i → i ≤ xs.length → xs.getD (i - 1) 0 ≠ 0 := by
    intro i h1 h2
    have : xs.getD (i - 1) 0 = xs[i - 1]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp
    rw [this]; exact hlits _ (List.getElem_mem _)
  have hcs : ∀ i, 1 ≤ i → i ≤ xs.length →
      cl τ xs i = cl τ xs (i - 1) + (if litTrue τ (xs.getD (i - 1) 0) then 1 else 0) := by
    intro i h1 h2
    have := cl_succ τ xs (i := i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this; exact this
  have hrp : ∀ i j, 0 < reg base k i j := by intro i j; unfold reg; omega
  intro c hc
  unfold atMost at hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.mem_flatMap] at hc
  rcases hc with (hc | ⟨j0, hj0, rfl⟩) | ⟨i0, hi0, hc⟩
  · -- [¬x1, R(1,1)]
    subst hc
    simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    rw [litTrue_negLit τ (hx 1 (by omega) hn), litTrue_pos τ (hrp _ _), hR 1 1 (by omega) hn (by omega) hk]
    have := hcs 1 (by omega) hn; rw [cl_zero] at this
    cases h : litTrue τ (xs.getD (1 - 1) 0) <;> simp_all
  · -- ¬R(1, j0+2)
    simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false]
    rw [litTrue_neg τ (hrp _ _), hR 1 (j0 + 2) (by omega) hn (by omega) (by omega)]
    have := hcs 1 (by omega) hn; rw [cl_zero] at this
    have : cl τ xs 1 ≤ 1 := by split at this <;> omega
    simp; omega
  · have hi : i0 + 2 ≤ xs.length := by omega
    have hstep := hcs (i0 + 2) (by omega) hi
    have hxi := hx (i0 + 2) (by omega) hi
    have hm := cl_mono τ xs (show i0 + 2 ≤ xs.length from hi)
    rcases hc with rfl | rfl | rfl | ⟨j0, hj0, hc⟩
    · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [litTrue_negLit τ hxi, litTrue_pos τ (hrp _ _), hR (i0 + 2) 1 (by omega) hi (by omega) hk]
      cases h : litTrue τ (xs.getD (i0 + 2 - 1) 0) <;> simp_all
    · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [litTrue_neg τ (hrp _ _), litTrue_pos τ (hrp _ _), hR (i0 + 2) 1 (by omega) hi (by omega) hk,
        hR (i0 + 2 - 1) 1 (by omega) (by omega) (by omega) hk]
      simp only [show i0 + 2 - 1 = i0 + 1 by omega] at hstep ⊢; simp; split at hstep <;> omega
    · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [litTrue_negLit τ hxi, litTrue_neg τ (hrp _ _), hR (i0 + 2 - 1) k (by omega) (by omega) hk (Nat.le_refl _)]
      cases h : litTrue τ (xs.getD (i0 + 2 - 1) 0) <;> simp_all <;> omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [litTrue_negLit τ hxi, litTrue_neg τ (hrp _ _), litTrue_pos τ (hrp _ _),
          hR (i0 + 2) (j0 + 2) (by omega) hi (by omega) (by omega),
          hR (i0 + 2 - 1) (j0 + 2 - 1) (by omega) (by omega) (by omega) (by omega)]
        cases h : litTrue τ (xs.getD (i0 + 2 - 1) 0) <;> simp_all <;> omega
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [litTrue_neg τ (hrp _ _), litTrue_pos τ (hrp _ _),
          hR (i0 + 2) (j0 + 2) (by omega) hi (by omega) (by omega),
          hR (i0 + 2 - 1) (j0 + 2) (by omega) (by omega) (by omega) (by omega)]
        simp only [show i0 + 2 - 1 = i0 + 1 by omega] at hstep ⊢; simp; split at hstep <;> omega

end Dim8Lift.Cnf
