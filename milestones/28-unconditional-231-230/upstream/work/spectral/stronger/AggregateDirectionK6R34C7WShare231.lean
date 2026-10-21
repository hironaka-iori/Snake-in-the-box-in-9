import AggregateDirectionK6R34C7WConditional
import EmptyShareBound

/-!
# Conditional 231: the 232 chain plus a uniform empty-square share bonus

The 232 chain (`WindowAutomatonK6R34C7W*`, L = 7 directions of memory, k = 6 centres, cap 7,
mean 9/2) proves the walk inequality `total_boundK6R34C7W`; restated for a snake it reads

    9 m ≤ 2 Σ_{j=1}^{m-1} α_j + 59                                   (`walk_232_K6R34C7W`)

(steps i = 0 .. m-8 of the telescoped potential add the counts of vertices 7 .. m-1; vertices
1 .. 6 are paid by the start potential, `D = -2`, and `α_1 ≥ 1`).

The new premise concerns the *window of step i*: directions `pathDir p j .. pathDir p (j+6)`
(vertices j .. j+7) with j = i+1, centres j+1 .. j+6.  This is exactly the six-centre window
that `hw6 j` of the 232 theorem constrains.  The premise is: for every listed direction shape
`s ∈ shapesK6R34C7W` (the 34 canonical seven-direction shapes of the chain, first-occurrence
relabelling, *not* identified under reversal), every window of shape `s` with `1 ≤ j`,
`j + 7 ≤ m` has share sum at least 21 (`windowShare`, with `share` from `EmptyShareBound`,
weights 6/3/2).  `window_shape_mem` proves (kernel check over the 877 restricted growth strings
of length 7) that every window of a snake has one of the 34 listed shapes, so the per-shape
premise is equivalent to the plain `∀ j, 21 ≤ windowShare p j`.

Accounting: every centre j+1 .. j+6 is an internal vertex, and a vertex is a centre of at most
six of the m-7 windows, so `Σ_j windowShare ≤ 6 · totalShare` (`sum_windowShare_le`), and
`4 · totalShare ≤ 42 · totalEmptyAnchored = 42 · 4 s0` (`totalShare_le`), which is folded into
`weighted_identity_bound : 21 T + totalShare + 735 (m+1) ≤ 21 · 9214`.  The start potential `D`
of the chain is not reused or rescaled: the bonus is added to the final inequality, giving
`1666 m ≤ 386470`, i.e. m ≤ 231 (231.97).
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton
noncomputable section
set_option maxHeartbeats 1600000

/-! ## 1. The walk inequality of the 232 chain -/

/-- The intermediate inequality of the conditional-232 chain, before the incidence identity:
`9 m ≤ 2 Σ_{j=1}^{m-1} α_j + 59`, under the same 15,959 window premises. -/
theorem walk_232_K6R34C7W {m : Nat} (p : Snake m) (hm : 7 ≤ m)
    (hw2 : ∀ j, j + 3 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5))] = false)
    (hw6 : ∀ j, j + 7 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5), pathDir p (j+6)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5)), symK 8 (countSeq p (j+6))] = false) :
    9 * m ≤ 2 * psum (fun j => countSeq p (j+1)) (m-1) + 59 := by
  obtain ⟨_, _, hpos, _, _⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ countSeq p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    simpa [show j - 1 + 1 = j by omega] using this
  have htot := total_boundK6R34C7W (pathDir p) (countSeq p) m hm hpos'
    (fun i hi => by rw [winK6R34C7W_eq]; exact snake_inducedPattern_block p i 8 hi) hw2 hw3 hw4 hw5 hw6
  rw [sumA_eq_psum] at htot
  exact htot

/-! ## 2. Window shares -/

/-- `share` of the k-th path vertex, padded by zero (like `countSeq`). -/
def shareSeq {m : Nat} (p : Snake m) (k : Nat) : Nat :=
  if hk : k < m + 1 then share p ⟨k, hk⟩ else 0

/-- Directions of window `j`: the seven edges from vertex `j` to vertex `j+7`
(the window of premise `hw6 j`). -/
def windowDirs {m : Nat} (p : Snake m) (j : Nat) : List Nat :=
  [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5),
    pathDir p (j+6)]

/-- Share sum over the six centres `j+1 .. j+6` of window `j`. -/
def windowShare {m : Nat} (p : Snake m) (j : Nat) : Nat :=
  shareSeq p (j+1) + shareSeq p (j+2) + shareSeq p (j+3) + shareSeq p (j+4) + shareSeq p (j+5) +
    shareSeq p (j+6)

theorem windowDirs_eq {m : Nat} (p : Snake m) (j : Nat) : windowDirs p j = blockList p j 7 := rfl

theorem totalShare_eq_range {m : Nat} (p : Snake m) :
    totalShare p = ∑ c ∈ Finset.range (m + 1), shareSeq p c := by
  unfold totalShare
  rw [Finset.sum_range (fun c => shareSeq p c)]
  apply Finset.sum_congr rfl
  intro i _
  simp [shareSeq, i.isLt]

/-! ### Every window has one of the 34 listed shapes -/

/-- Kernel check: every restricted growth string of length 7 passing the xor-mask induced test
has its code in the shape bitset of the chain. -/
theorem rgs7K6R34C7W_shape : letN (shapeMaskK6R34C7W + 1) (fun M => allRGS 7 0 (fun c =>
    !inducedFast c || Nat.testBit M (shapeCode c))) = true := by
  decide +kernel

theorem window_shape_mem {m : Nat} (p : Snake m) (j : Nat) (hj : j + 7 ≤ m) :
    canon (windowDirs p j) ∈ shapesK6R34C7W := by
  have hm := rgs7K6R34C7W_shape
  rw [letN_succ] at hm
  have hlen : (canon (windowDirs p j)).length = 7 := by rw [length_canon]; rfl
  have hr := canon_isRGS (windowDirs p j)
  have hm := allRGS_spec 7 0 _ hm _ hlen hr
  have hind : inducedPattern (canon (windowDirs p j)) = true := by
    rw [inducedPattern_canon, windowDirs_eq]; exact snake_inducedPattern_block p j 7 hj
  have hb : ∀ a, a ∈ canon (windowDirs p j) → a < 8 := fun a ha => by
    have := isRGS_bound _ 0 hr a ha; rw [hlen] at this; omega
  have hfast := inducedFast_of_inducedPattern _ (fun d hd => by have := hb d hd; omega) hind
  rw [hfast] at hm
  simp only [Bool.not_true, Bool.false_or] at hm
  obtain ⟨s, hs, hcode⟩ := testBit_maskOf _ _ _ hm
  have hsh : s.length = 7 ∧ ∀ a, a ∈ s → a < 8 := by
    have hall := shapesK6R34C7W_ok
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
    exact hall s hs
  unfold shapeCode at hcode
  rw [codeFrom_inj _ s 1 (by rw [hlen, hsh.1]) hb hsh.2 hcode.symm]
  exact hs

/-! ### Multiplicity: each vertex is a centre of at most six windows -/

theorem shift_sum_le (f : Nat → Nat) (n t N : Nat) (h : t + n ≤ N) :
    ∑ j ∈ Finset.range n, f (j + t) ≤ ∑ c ∈ Finset.range N, f c := by
  calc ∑ j ∈ Finset.range n, f (j + t)
      = ∑ j ∈ Finset.range n, f (t + j) := by
        apply Finset.sum_congr rfl; intro j _; rw [Nat.add_comm]
    _ ≤ ∑ c ∈ Finset.range t, f c + ∑ j ∈ Finset.range n, f (t + j) := Nat.le_add_left _ _
    _ = ∑ c ∈ Finset.range (t + n), f c := (Finset.sum_range_add f t n).symm
    _ ≤ ∑ c ∈ Finset.range N, f c :=
        Finset.sum_le_sum_of_subset (Finset.range_subset.mpr h)

/-- The windows `j = 1 .. m-7` (one per step of the chain) have total share at most six times
the total share of the path. -/
theorem sum_windowShare_le {m : Nat} (p : Snake m) (hm : 7 ≤ m) :
    ∑ i ∈ Finset.range (m - 7), windowShare p (i + 1) ≤ 6 * totalShare p := by
  have he : ∀ i, windowShare p (i + 1) = shareSeq p (i + 2) + shareSeq p (i + 3) +
      shareSeq p (i + 4) + shareSeq p (i + 5) + shareSeq p (i + 6) + shareSeq p (i + 7) :=
    fun i => rfl
  simp only [he, Finset.sum_add_distrib]
  rw [totalShare_eq_range]
  have h2 := shift_sum_le (shareSeq p) (m - 7) 2 (m + 1) (by omega)
  have h3 := shift_sum_le (shareSeq p) (m - 7) 3 (m + 1) (by omega)
  have h4 := shift_sum_le (shareSeq p) (m - 7) 4 (m + 1) (by omega)
  have h5 := shift_sum_le (shareSeq p) (m - 7) 5 (m + 1) (by omega)
  have h6 := shift_sum_le (shareSeq p) (m - 7) 6 (m + 1) (by omega)
  have h7 := shift_sum_le (shareSeq p) (m - 7) 7 (m + 1) (by omega)
  omega

/-! ## 3. The conditional 231 -/

theorem totalSingleton_split {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    (∑ i, localAlpha p i) = countSeq p 0 + psum (fun j => countSeq p (j+1)) (m-1) + countSeq p m := by
  rw [Finset.sum_fin_eq_sum_range]
  have hc : (∑ j ∈ Finset.range (m+1), if h : j < m + 1 then localAlpha p ⟨j, h⟩ else 0) =
      ∑ j ∈ Finset.range (m+1), countSeq p j := by
    apply Finset.sum_congr rfl; intro j _; rfl
  rw [hc, psum_eq_sum, Finset.sum_range_succ]
  have he : Finset.range m = Finset.range ((m-1)+1) := by congr 1; omega
  rw [he, Finset.sum_range_succ']
  omega

/-- Conditional 231, plain form of the share premise: every window `j` (`1 ≤ j`, `j + 7 ≤ m`)
has share sum at least 21. -/
theorem upper_231_of_direction_windows_and_shares_all {m : Nat} (p : Snake m)
    (hw2 : ∀ j, j + 3 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5))] = false)
    (hw6 : ∀ j, j + 7 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5), pathDir p (j+6)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5)), symK 8 (countSeq p (j+6))] = false)
    (hshare : ∀ j, 1 ≤ j → j + 7 ≤ m → 21 ≤ windowShare p j) : m ≤ 231 := by
  by_cases hm : m < 7
  · omega
  have hwalk := walk_232_K6R34C7W p (by omega) hw2 hw3 hw4 hw5 hw6
  obtain ⟨h0, h1, _, _, _⟩ := countSeq_facts p (by omega)
  have hsplit := totalSingleton_split p (by omega)
  have hwt := weighted_identity_bound p (by omega)
  have hmul := sum_windowShare_le p (by omega)
  have hlow : 21 * (m - 7) ≤ ∑ i ∈ Finset.range (m - 7), windowShare p (i + 1) := by
    have := Finset.sum_le_sum (s := Finset.range (m - 7)) (f := fun _ => 21)
      (g := fun i => windowShare p (i + 1)) (fun i hi => hshare (i + 1) (by omega)
        (by have := Finset.mem_range.mp hi; omega))
    simpa [Nat.mul_comm] using this
  rw [hsplit] at hwt
  omega

/-- **Conditional 231-edge bound.**  Premises: the 15,959 window exclusions of the 232 chain
(`hw2` .. `hw6`, unchanged) and, for each of the 34 six-centre direction shapes of the chain,
that no window of that shape has share sum at most 20.  Neither premise is proved in Lean. -/
theorem upper_231_of_direction_windows_and_shares {m : Nat} (p : Snake m)
    (hw2 : ∀ j, j + 3 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2))] = false)
    (hw3 : ∀ j, j + 4 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3))] = false)
    (hw4 : ∀ j, j + 5 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4))] = false)
    (hw5 : ∀ j, j + 6 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5))] = false)
    (hw6 : ∀ j, j + 7 ≤ m → wforbK6R34C7W [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4), pathDir p (j+5), pathDir p (j+6)]
      [symK 8 (countSeq p (j+1)), symK 8 (countSeq p (j+2)), symK 8 (countSeq p (j+3)), symK 8 (countSeq p (j+4)), symK 8 (countSeq p (j+5)), symK 8 (countSeq p (j+6))] = false)
    (hshare : ∀ s ∈ shapesK6R34C7W, ∀ j, 1 ≤ j → j + 7 ≤ m →
      canon (windowDirs p j) = s → 21 ≤ windowShare p j) : m ≤ 231 :=
  upper_231_of_direction_windows_and_shares_all p hw2 hw3 hw4 hw5 hw6
    (fun j h1 h7 => hshare _ (window_shape_mem p j h7) j h1 h7 rfl)

#print axioms walk_232_K6R34C7W
#print axioms window_shape_mem
#print axioms sum_windowShare_le
#print axioms upper_231_of_direction_windows_and_shares_all
#print axioms upper_231_of_direction_windows_and_shares
end
end Snake9
