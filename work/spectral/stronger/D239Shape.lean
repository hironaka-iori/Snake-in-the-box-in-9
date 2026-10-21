import D239Table
/-!
# Direction-aware windows: normalisation and the three window premises

`norm2` generalises `WinShape.norm` to windows with repeated directions: the cube automorphism
sends the distinct directions (listed by first position) to `0, 1, 2, ...`; equal directions stay
equal, and the table predicate `wforb1` of any list of edge directions is unchanged, because a
coordinate permutation is injective on the labels (`canon_map`).

Along a snake the edge directions of a window have one of the shapes `012` (two centres),
`0120`, `0123` (three centres), `01203`, `01230`, `01231`, `01234` (four centres; `abcab` is a
chord, `WinShape.dir_chord`).  `wforb ds syms` flags the window read forwards or backwards; in
each case the snake is normalised in the reading direction, so the window becomes `0,1,3,7,...`
and the flagged table entry is covered by a certified range tuple (`D239Table`), whose
refutation (hypotheses `hL*`) gives a contradiction.  The shape `01231` is never flagged; read
backwards it is `01203`.
-/
namespace D239
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1 Snake9.WindowAutomaton WinShape

section
variable {m : Nat}

theorem norm2 (p : Snake m) (b : Nat) (hb : b ≤ m) (l : List Nat)
    (hnd : (l.map (dirC p)).Nodup) (hl : ∀ j ∈ l, j < m) :
    ∃ q : Snake m, q.vertex ⟨b, by omega⟩ = 0 ∧
      (∀ i (h : i < l.length), pathDir q l[i] = i) ∧
      (∀ k, localAlpha q k = localAlpha p k) ∧
      (∀ j j', j < m → j' < m → dirC p j = dirC p j' → pathDir q j = pathDir q j') ∧
      (∀ w : List Nat, (∀ j ∈ w, j < m) → ∀ ss,
        wforb1 (w.map (pathDir p)) ss = true → wforb1 (w.map (pathDir q)) ss = true) := by
  obtain ⟨σ, x, h0, hd, ha⟩ := CubePerm.exists_normalizing_cubeMap p ⟨b, by omega⟩ l hnd hl
  refine ⟨_, h0, hd, ha, fun j j' hj hj' he => ?_, fun w hw ss hs => ?_⟩
  · rw [CubePerm.pathDir_cubeMap σ x p j hj, CubePerm.pathDir_cubeMap σ x p j' hj']
    exact congrArg (fun c => (σ c).val) he
  · let f : Nat → Nat := fun n => if h : n < 9 then (σ ⟨n, h⟩).val else n
    have hmap : w.map (pathDir (CubePerm.cubeMap σ x p)) = (w.map (pathDir p)).map f := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      rw [CubePerm.pathDir_cubeMap σ x p j (hw j hj)]
      simp [f, pathDir_lt p j]
    have hinj : ∀ a ∈ w.map (pathDir p), ∀ b ∈ w.map (pathDir p), f a = f b → a = b := by
      intro a ha b hb hab
      obtain ⟨ja, -, rfl⟩ := List.mem_map.mp ha
      obtain ⟨jb, -, rfl⟩ := List.mem_map.mp hb
      simp only [f, pathDir_lt p ja, pathDir_lt p jb, dif_pos] at hab
      exact congrArg Fin.val (σ.injective (Fin.ext hab))
    unfold wforb1 at hs ⊢
    rw [hmap, canon_map f _ hinj]
    exact hs

/-! ### Two centres -/

theorem no_w2 {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P2 x) (ht : tab2 [0, 1, 2] L = true)
    (p : Snake m) (j : Nat) (hj : j + 3 ≤ m) :
    wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2))] = false := by
  have n01 : dirC p j ≠ dirC p (j+1) := dir_ne_succ p j (by omega)
  have n12 : dirC p (j+1) ≠ dirC p (j+2) := dir_ne_succ p (j+1) (by omega)
  have n02 : dirC p j ≠ dirC p (j+2) := dir_ne_succ_succ p j (by omega)
  rw [countSeq_eq p (j+1) (by omega), countSeq_eq p (j+2) (by omega)]
  cases hw : wforb _ _ with
  | false => rfl
  | true =>
    exfalso
    unfold wforb at hw
    simp only [Bool.or_eq_true, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append] at hw
    rcases hw with hF | hB
    · obtain ⟨q, v0, hd, ha, -, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2]
        (nodup3 n01 n02 n12) (by intro i hi; simp at hi; omega)
      have d0 : pathDir q j = 0 := hd 0 (by simp)
      have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
      have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
      have v1 := stepF q j (by omega) 0 d0 v0 (w := 1) (by decide)
      have v2 := stepF q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
      have v3 := stepF q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
      have hq := hwq [j, j+1, j+2] (by intro i hi; simp at hi; omega) _ hF
      simp only [List.map_cons, List.map_nil, d0, d1, d2, ← ha] at hq
      exact duoF_tab q hL ht j hj v0 v1 v2 v3 hq
    · obtain ⟨q, v0, hd, ha, -, hwq⟩ := norm2 p (j+3) (by omega) [j+2, j+1, j]
        (nodup3 (Ne.symm n12) (Ne.symm n02) (Ne.symm n01)) (by intro i hi; simp at hi; omega)
      have d0 : pathDir q (j+2) = 0 := hd 0 (by simp)
      have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
      have d2 : pathDir q j = 2 := hd 2 (by simp)
      have v1 := stepB q (j+2) (by omega) 0 d0 v0 (w := 1) (by decide)
      have v2 := stepB q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
      have v3 := stepB q j (by omega) 2 d2 v2 (w := 7) (by decide)
      have hq := hwq [j+2, j+1, j] (by intro i hi; simp at hi; omega) _ hB
      simp only [List.map_cons, List.map_nil, d0, d1, d2, ← ha] at hq
      exact duoB_tab q hL ht j hj v0 v1 v2 v3 hq

/-! ### Three centres -/

theorem no_w3 {LA LB : List (List (Nat × Nat))} (hA : ∀ x ∈ LA, P3 0 x) (hB : ∀ x ∈ LB, P3 3 x)
    (tA : tab3 [0, 1, 2, 0] LA = true) (tB : tab3 [0, 1, 2, 3] LB = true)
    (p : Snake m) (j : Nat) (hj : j + 4 ≤ m) :
    wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3))] = false := by
  have n01 : dirC p j ≠ dirC p (j+1) := dir_ne_succ p j (by omega)
  have n12 : dirC p (j+1) ≠ dirC p (j+2) := dir_ne_succ p (j+1) (by omega)
  have n23 : dirC p (j+2) ≠ dirC p (j+3) := dir_ne_succ p (j+2) (by omega)
  have n02 : dirC p j ≠ dirC p (j+2) := dir_ne_succ_succ p j (by omega)
  have n13 : dirC p (j+1) ≠ dirC p (j+3) := dir_ne_succ_succ p (j+1) (by omega)
  rw [countSeq_eq p (j+1) (by omega), countSeq_eq p (j+2) (by omega),
    countSeq_eq p (j+3) (by omega)]
  have hl4 : ∀ l : List Nat, (∀ i ∈ l, i ≤ j + 3) → ∀ i ∈ l, i < m :=
    fun l h i hi => by have := h i hi; omega
  cases hw : wforb _ _ with
  | false => rfl
  | true =>
    exfalso
    unfold wforb at hw
    simp only [Bool.or_eq_true, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append] at hw
    by_cases h30 : dirC p (j+3) = dirC p j
    · rcases hw with hF | hR
      · obtain ⟨q, v0, hd, ha, htr, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2]
          (nodup3 n01 n02 n12) (hl4 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q j = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+3) = 0 := (htr _ _ (by omega) (by omega) h30).trans d0
        have v1 := stepF q j (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepF q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepF q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepF q (j+3) (by omega) 0 d3 v3 rfl
        have hq := hwq [j, j+1, j+2, j+3] (hl4 _ (by intro i hi; simp at hi; omega)) _ hF
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, ← ha] at hq
        exact triF_tab q hA tA cok7r j hj v0 v1 v2 v3 v4 hq
      · obtain ⟨q, v0, hd, ha, htr, hwq⟩ := norm2 p (j+4) (by omega) [j+3, j+2, j+1]
          (nodup3 (Ne.symm n23) (Ne.symm n13) (Ne.symm n12)) (hl4 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q (j+3) = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+2) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+1) = 2 := hd 2 (by simp)
        have d3 : pathDir q j = 0 := (htr _ _ (by omega) (by omega) h30.symm).trans d0
        have v1 := stepB q (j+3) (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepB q (j+2) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepB q (j+1) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepB q j (by omega) 0 d3 v3 rfl
        have hq := hwq [j+3, j+2, j+1, j] (hl4 _ (by intro i hi; simp at hi; omega)) _ hR
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, ← ha] at hq
        exact triB_tab q hA tA cok7r j hj v0 v1 v2 v3 v4 hq
    · rcases hw with hF | hR
      · obtain ⟨q, v0, hd, ha, -, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2, j+3]
          (nodup4 n01 n02 (Ne.symm h30) n12 n13 n23) (hl4 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q j = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+3) = 3 := hd 3 (by simp)
        have v1 := stepF q j (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepF q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepF q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepF q (j+3) (by omega) 3 d3 v3 rfl
        have hq := hwq [j, j+1, j+2, j+3] (hl4 _ (by intro i hi; simp at hi; omega)) _ hF
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, ← ha] at hq
        exact triF_tab q hB tB cok7d j hj v0 v1 v2 v3 v4 hq
      · obtain ⟨q, v0, hd, ha, -, hwq⟩ := norm2 p (j+4) (by omega) [j+3, j+2, j+1, j]
          (nodup4 (Ne.symm n23) (Ne.symm n13) h30 (Ne.symm n12) (Ne.symm n02) (Ne.symm n01))
          (hl4 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q (j+3) = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+2) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+1) = 2 := hd 2 (by simp)
        have d3 : pathDir q j = 3 := hd 3 (by simp)
        have v1 := stepB q (j+3) (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepB q (j+2) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepB q (j+1) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepB q j (by omega) 3 d3 v3 rfl
        have hq := hwq [j+3, j+2, j+1, j] (hl4 _ (by intro i hi; simp at hi; omega)) _ hR
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, ← ha] at hq
        exact triB_tab q hB tB cok7d j hj v0 v1 v2 v3 v4 hq

/-! ### Four centres -/

theorem no_w4 {LA LB LC : List (List (Nat × Nat))} (hA : ∀ x ∈ LA, P4 0 3 x)
    (hB : ∀ x ∈ LB, P4 3 0 x) (hC : ∀ x ∈ LC, P4 3 4 x)
    (tA : tab4 [0, 1, 2, 0, 3] LA = true) (tB : tab4 [0, 1, 2, 3, 0] LB = true)
    (tC : tab4 [0, 1, 2, 3, 4] LC = true) (tN : tab4 [0, 1, 2, 3, 1] [] = true)
    (p : Snake m) (j : Nat) (hj : j + 5 ≤ m) :
    wforb [pathDir p j, pathDir p (j+1), pathDir p (j+2), pathDir p (j+3), pathDir p (j+4)]
      [sym (countSeq p (j+1)), sym (countSeq p (j+2)), sym (countSeq p (j+3)),
        sym (countSeq p (j+4))] = false := by
  have n01 : dirC p j ≠ dirC p (j+1) := dir_ne_succ p j (by omega)
  have n12 : dirC p (j+1) ≠ dirC p (j+2) := dir_ne_succ p (j+1) (by omega)
  have n23 : dirC p (j+2) ≠ dirC p (j+3) := dir_ne_succ p (j+2) (by omega)
  have n34 : dirC p (j+3) ≠ dirC p (j+4) := dir_ne_succ p (j+3) (by omega)
  have n02 : dirC p j ≠ dirC p (j+2) := dir_ne_succ_succ p j (by omega)
  have n13 : dirC p (j+1) ≠ dirC p (j+3) := dir_ne_succ_succ p (j+1) (by omega)
  have n24 : dirC p (j+2) ≠ dirC p (j+4) := dir_ne_succ_succ p (j+2) (by omega)
  rw [countSeq_eq p (j+1) (by omega), countSeq_eq p (j+2) (by omega),
    countSeq_eq p (j+3) (by omega), countSeq_eq p (j+4) (by omega)]
  have hl5 : ∀ l : List Nat, (∀ i ∈ l, i ≤ j + 4) → ∀ i ∈ l, i < m :=
    fun l h i hi => by have := h i hi; omega
  cases hw : wforb _ _ with
  | false => rfl
  | true =>
    exfalso
    unfold wforb at hw
    simp only [Bool.or_eq_true, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append] at hw
    by_cases h30 : dirC p (j+3) = dirC p j
    · -- shape 01203; backwards 01231
      have h41 : dirC p (j+4) ≠ dirC p (j+1) := fun h => dir_chord p j hj h30 h
      have h40 : dirC p (j+4) ≠ dirC p j := fun h => n34 (h30.trans h.symm)
      rcases hw with hF | hR
      · obtain ⟨q, v0, hd, ha, htr, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2, j+4]
          (nodup4 n01 n02 (Ne.symm h40) n12 (Ne.symm h41) n24)
          (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q j = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d4 : pathDir q (j+4) = 3 := hd 3 (by simp)
        have d3 : pathDir q (j+3) = 0 := (htr _ _ (by omega) (by omega) h30).trans d0
        have v1 := stepF q j (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepF q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepF q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepF q (j+3) (by omega) 0 d3 v3 rfl
        have v5 := stepF q (j+4) (by omega) 3 d4 v4 rfl
        have hq := hwq [j, j+1, j+2, j+3, j+4] (hl5 _ (by intro i hi; simp at hi; omega)) _ hF
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4, ← ha] at hq
        exact quadF_tab q hA tA cok7r cok6' j hj v0 v1 v2 v3 v4 v5 hq
      · obtain ⟨q, -, hd, -, htr, hwq⟩ := norm2 p (j+5) (by omega) [j+4, j+3, j+2, j+1]
          (nodup4 (Ne.symm n34) (Ne.symm n24) h41 (Ne.symm n23) (Ne.symm n13) (Ne.symm n12))
          (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q (j+4) = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+3) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+1) = 3 := hd 3 (by simp)
        have d4 : pathDir q j = 1 := (htr _ _ (by omega) (by omega) h30.symm).trans d1
        have hq := hwq [j+4, j+3, j+2, j+1, j] (hl5 _ (by intro i hi; simp at hi; omega)) _ hR
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4] at hq
        exact none4 tN hq
    by_cases h40 : dirC p (j+4) = dirC p j
    · -- shape 01230, symmetric
      have h41 : dirC p (j+4) ≠ dirC p (j+1) := by rw [h40]; exact n01
      rcases hw with hF | hR
      · obtain ⟨q, v0, hd, ha, htr, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2, j+3]
          (nodup4 n01 n02 (Ne.symm h30) n12 n13 n23) (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q j = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+3) = 3 := hd 3 (by simp)
        have d4 : pathDir q (j+4) = 0 := (htr _ _ (by omega) (by omega) h40).trans d0
        have v1 := stepF q j (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepF q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepF q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepF q (j+3) (by omega) 3 d3 v3 rfl
        have v5 := stepF q (j+4) (by omega) 0 d4 v4 rfl
        have hq := hwq [j, j+1, j+2, j+3, j+4] (hl5 _ (by intro i hi; simp at hi; omega)) _ hF
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4, ← ha] at hq
        exact quadF_tab q hB tB cok7d cok15a' j hj v0 v1 v2 v3 v4 v5 hq
      · obtain ⟨q, v0, hd, ha, htr, hwq⟩ := norm2 p (j+5) (by omega) [j+4, j+3, j+2, j+1]
          (nodup4 (Ne.symm n34) (Ne.symm n24) h41 (Ne.symm n23) (Ne.symm n13) (Ne.symm n12))
          (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q (j+4) = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+3) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+1) = 3 := hd 3 (by simp)
        have d4 : pathDir q j = 0 := (htr _ _ (by omega) (by omega) h40.symm).trans d0
        have v1 := stepB q (j+4) (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepB q (j+3) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepB q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepB q (j+1) (by omega) 3 d3 v3 rfl
        have v5 := stepB q j (by omega) 0 d4 v4 rfl
        have hq := hwq [j+4, j+3, j+2, j+1, j] (hl5 _ (by intro i hi; simp at hi; omega)) _ hR
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4, ← ha] at hq
        exact quadB_tab q hB tB cok7d cok15a' j hj v0 v1 v2 v3 v4 v5 hq
    by_cases h41 : dirC p (j+4) = dirC p (j+1)
    · -- shape 01231; backwards 01203
      rcases hw with hF | hR
      · obtain ⟨q, -, hd, -, htr, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2, j+3]
          (nodup4 n01 n02 (Ne.symm h30) n12 n13 n23) (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q j = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+3) = 3 := hd 3 (by simp)
        have d4 : pathDir q (j+4) = 1 := (htr _ _ (by omega) (by omega) h41).trans d1
        have hq := hwq [j, j+1, j+2, j+3, j+4] (hl5 _ (by intro i hi; simp at hi; omega)) _ hF
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4] at hq
        exact none4 tN hq
      · obtain ⟨q, v0, hd, ha, htr, hwq⟩ := norm2 p (j+5) (by omega) [j+4, j+3, j+2, j]
          (nodup4 (Ne.symm n34) (Ne.symm n24) h40 (Ne.symm n23) h30 (Ne.symm n02))
          (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q (j+4) = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+3) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d4 : pathDir q j = 3 := hd 3 (by simp)
        have d3 : pathDir q (j+1) = 0 := (htr _ _ (by omega) (by omega) h41.symm).trans d0
        have v1 := stepB q (j+4) (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepB q (j+3) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepB q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepB q (j+1) (by omega) 0 d3 v3 rfl
        have v5 := stepB q j (by omega) 3 d4 v4 rfl
        have hq := hwq [j+4, j+3, j+2, j+1, j] (hl5 _ (by intro i hi; simp at hi; omega)) _ hR
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4, ← ha] at hq
        exact quadB_tab q hA tA cok7r cok6' j hj v0 v1 v2 v3 v4 v5 hq
    · -- shape 01234
      rcases hw with hF | hR
      · obtain ⟨q, v0, hd, ha, -, hwq⟩ := norm2 p j (by omega) [j, j+1, j+2, j+3, j+4]
          (nodup5 n01 n02 (Ne.symm h30) (Ne.symm h40) n12 n13 (Ne.symm h41) n23 n24 n34)
          (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q j = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+1) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+3) = 3 := hd 3 (by simp)
        have d4 : pathDir q (j+4) = 4 := hd 4 (by simp)
        have v1 := stepF q j (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepF q (j+1) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepF q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepF q (j+3) (by omega) 3 d3 v3 rfl
        have v5 := stepF q (j+4) (by omega) 4 d4 v4 rfl
        have hq := hwq [j, j+1, j+2, j+3, j+4] (hl5 _ (by intro i hi; simp at hi; omega)) _ hF
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4, ← ha] at hq
        exact quadF_tab q hC tC cok7d cok15b' j hj v0 v1 v2 v3 v4 v5 hq
      · obtain ⟨q, v0, hd, ha, -, hwq⟩ := norm2 p (j+5) (by omega) [j+4, j+3, j+2, j+1, j]
          (nodup5 (Ne.symm n34) (Ne.symm n24) h41 h40 (Ne.symm n23) (Ne.symm n13) h30
            (Ne.symm n12) (Ne.symm n02) (Ne.symm n01))
          (hl5 _ (by intro i hi; simp at hi; omega))
        have d0 : pathDir q (j+4) = 0 := hd 0 (by simp)
        have d1 : pathDir q (j+3) = 1 := hd 1 (by simp)
        have d2 : pathDir q (j+2) = 2 := hd 2 (by simp)
        have d3 : pathDir q (j+1) = 3 := hd 3 (by simp)
        have d4 : pathDir q j = 4 := hd 4 (by simp)
        have v1 := stepB q (j+4) (by omega) 0 d0 v0 (w := 1) (by decide)
        have v2 := stepB q (j+3) (by omega) 1 d1 v1 (w := 3) (by decide)
        have v3 := stepB q (j+2) (by omega) 2 d2 v2 (w := 7) (by decide)
        have v4 := stepB q (j+1) (by omega) 3 d3 v3 rfl
        have v5 := stepB q j (by omega) 4 d4 v4 rfl
        have hq := hwq [j+4, j+3, j+2, j+1, j] (hl5 _ (by intro i hi; simp at hi; omega)) _ hR
        simp only [List.map_cons, List.map_nil, d0, d1, d2, d3, d4, ← ha] at hq
        exact quadB_tab q hC tC cok7d cok15b' j hj v0 v1 v2 v3 v4 v5 hq

end

end D239
