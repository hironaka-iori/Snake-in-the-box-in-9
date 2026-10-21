import WinShape
/-!
# Lex-leader symmetry breaking for window CNFs

A window in normal position uses only the coordinates of a list `W`; every permutation of the
other ("free") coordinates fixes the window vertices and all local counts.  Among the images of a
snake under these permutations take one whose selection is lexicographically least (vertices
compared in a fixed order `ord`, `true > false`): `lexmin`.  For the transposition `σ` of two free
coordinates it satisfies `LexOKP S [(v, σ v) | v ∈ ord]`: the selection vector is at most its
`σ`-image.  Restricted to the moved vertices (`lexOK_filter`), this is what the lex-leader clauses
of the symmetry-broken window CNFs encode (auxiliary variable `e_i`: the first `i` pairs agree).
-/
namespace D239
open Snake9 Snake9.SquareIncidence WinCNF W223G1 Snake9.CubePerm

/-! ### Lexicographic comparison -/

/-- `S` along the first components is lexicographically at most `S` along the second ones. -/
def LexOKP (S : Nat → Bool) : List (Nat × Nat) → Prop
  | [] => True
  | p :: P => (S p.1 = true → S p.2 = true) ∧ (S p.1 = S p.2 → LexOKP S P)

/-- Big-endian value of a bit list. -/
def keyR : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 2 ^ l.length else 0) + keyR l

theorem keyR_lt : ∀ l : List Bool, keyR l < 2 ^ l.length
  | [] => by simp [keyR]
  | b :: l => by
    have := keyR_lt l
    simp only [keyR, List.length_cons, Nat.pow_succ]
    split <;> omega

theorem lex_of_key (S : Nat → Bool) (f : Nat → Nat) : ∀ ord : List Nat,
    keyR (ord.map S) ≤ keyR (ord.map (fun v => S (f v))) →
      LexOKP S (ord.map (fun v => (v, f v)))
  | [], _ => trivial
  | v :: ord, h => by
    simp only [List.map_cons, keyR, List.length_map] at h
    have h1 := keyR_lt (ord.map S)
    have h2 := keyR_lt (ord.map (fun v => S (f v)))
    simp only [List.length_map] at h1 h2
    refine ⟨fun hv => ?_, fun he => ?_⟩
    · cases hf : S (f v)
      · rw [hv, hf] at h; simp at h; omega
      · rfl
    · apply lex_of_key S f ord
      rw [he] at h
      split at h <;> omega

theorem lexOK_filter (S : Nat → Bool) : ∀ P : List (Nat × Nat),
    LexOKP S P → LexOKP S (P.filter (fun p => p.1 != p.2))
  | [], _ => trivial
  | p :: P, h => by
    obtain ⟨h1, h2⟩ := h
    by_cases hp : p.1 = p.2
    · have : (p.1 != p.2) = false := by simp [hp]
      rw [List.filter_cons, this]
      exact lexOK_filter S P (h2 (by rw [hp]))
    · have : (p.1 != p.2) = true := by simp [hp]
      rw [List.filter_cons, this]
      exact ⟨h1, fun he => lexOK_filter S P (h2 he)⟩

/-- The first `i` pairs agree. -/
def eqPre (S : Nat → Bool) (P : List (Nat × Nat)) (i : Nat) : Bool :=
  (P.take i).all (fun p => S p.1 == S p.2)

theorem lexAt (S : Nat → Bool) : ∀ (P : List (Nat × Nat)) (i : Nat), LexOKP S P → i < P.length →
    eqPre S P i = true → S (P.getD i (0, 0)).1 = true → S (P.getD i (0, 0)).2 = true
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | p :: P, 0, h, _, _, hx => h.1 hx
  | p :: P, i + 1, h, hi, he, hx => by
    simp only [eqPre, List.take_succ_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at he
    exact lexAt S P i (h.2 he.1) (by simp at hi; omega) he.2 hx

theorem eqPre_succ (S : Nat → Bool) (P : List (Nat × Nat)) (i : Nat) (hi : i < P.length) :
    eqPre S P (i + 1) = (eqPre S P i && (S (P.getD i (0, 0)).1 == S (P.getD i (0, 0)).2)) := by
  unfold eqPre
  rw [List.take_succ, List.all_append]
  congr 1
  simp [List.getD, List.getElem?_eq_getElem hi]

/-! ### Swapping two coordinates -/

/-- Swap bits `a` and `b` of `v`. -/
def swapN (a b v : Nat) : Nat :=
  if v.testBit a = v.testBit b then v else v ^^^ (2 ^ a ||| 2 ^ b)

theorem testBit_swapN (a b v j : Nat) :
    (swapN a b v).testBit j = v.testBit (if j = a then b else if j = b then a else j) := by
  unfold swapN
  by_cases ha : j = a <;> by_cases hb : j = b
  all_goals (split <;> rename_i h <;>
    simp_all [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow])
  all_goals first
    | (simp [show a ≠ j from fun e => ha e.symm, show b ≠ j from fun e => hb e.symm])
    | (cases h1 : v.testBit a <;> cases h2 : v.testBit b <;> simp_all)

theorem swapN_swapN (a b v : Nat) : swapN a b (swapN a b v) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_swapN, testBit_swapN]
  by_cases ha : j = a <;> by_cases hb : j = b <;> simp_all

theorem permV_swap_val (a b : Coord) (w : Vertex) :
    (permV (Equiv.swap a b) w).val = swapN a.val b.val w.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_swapN]
  by_cases hj : j < 9
  · have := testBit_permV (Equiv.swap a b) w ⟨j, hj⟩
    rw [this, Equiv.symm_swap, Equiv.swap_apply_def]
    by_cases ha : (⟨j, hj⟩ : Coord) = a
    · subst ha; simp
    · by_cases hb : (⟨j, hj⟩ : Coord) = b
      · subst hb
        have : j ≠ a.val := fun h => ha (Fin.ext h)
        simp [ha, this]
      · have h1 : j ≠ a.val := fun h => ha (Fin.ext h)
        have h2 : j ≠ b.val := fun h => hb (Fin.ext h)
        simp [ha, hb, h1, h2]
  · rw [vertex_testBit_high _ j (by omega)]
    have h1 : j ≠ a.val := by have := a.isLt; omega
    have h2 : j ≠ b.val := by have := b.isLt; omega
    simp only [h1, h2, if_false]
    rw [vertex_testBit_high _ j (by omega)]

theorem permV_trans (π σ : Equiv.Perm Coord) (w : Vertex) :
    permV (π.trans σ) w = permV σ (permV π w) := by
  apply vertex_ext
  intro c
  rw [testBit_permV, testBit_permV, testBit_permV]
  rfl

/-! ### The lex-least image -/

/-- Every set bit of `v` is a coordinate of `W`. -/
def BitsIn (W : List Coord) (v : Vertex) : Prop :=
  ∀ c : Coord, v.val.testBit c.val = true → c ∈ W

instance (W : List Coord) (v : Vertex) : Decidable (BitsIn W v) :=
  inferInstanceAs (Decidable (∀ c : Coord, _))

theorem permV_fix {W : List Coord} {π : Equiv.Perm Coord} (hπ : ∀ c ∈ W, π c = c) {v : Vertex}
    (hv : BitsIn W v) : permV π v = v := by
  apply vertex_ext
  intro a
  rw [testBit_permV]
  by_cases ha : a ∈ W
  · have : π.symm a = a := by
      rw [Equiv.symm_apply_eq]; exact (hπ a ha).symm
    rw [this]
  · have h1 : v.val.testBit a.val = false := by
      cases h : v.val.testBit a.val
      · rfl
      · exact absurd (hv a h) ha
    have h2 : π.symm a ∉ W := by
      intro hm
      have := hπ _ hm
      rw [Equiv.apply_symm_apply] at this
      exact ha (this ▸ hm)
    have h3 : v.val.testBit (π.symm a).val = false := by
      cases h : v.val.testBit (π.symm a).val
      · rfl
      · exact absurd (hv _ h) h2
    rw [h1, h3]

theorem lexmin {m : Nat} (q : Snake m) (W : List Coord) (ord : List Nat)
    (gens : List (Coord × Coord)) (hg : ∀ g ∈ gens, g.1 ∉ W ∧ g.2 ∉ W) :
    ∃ q' : Snake m, (∀ i, BitsIn W (q.vertex i) → q'.vertex i = q.vertex i) ∧
      (∀ k, localAlpha q' k = localAlpha q k) ∧
      ∀ g ∈ gens, LexOKP (sel q') (ord.map (fun v => (v, swapN g.1.val g.2.val v))) := by
  classical
  let G := (Finset.univ : Finset (Equiv.Perm Coord)).filter (fun π => ∀ c ∈ W, π c = c)
  have hne : G.Nonempty := ⟨1, by simp [G]⟩
  obtain ⟨π, hπ, hmin⟩ := G.exists_min_image
    (fun π => keyR (ord.map (sel (permSnake π q)))) hne
  have hπ' : ∀ c ∈ W, π c = c := (Finset.mem_filter.mp hπ).2
  refine ⟨permSnake π q, fun i hi => permV_fix hπ' hi, fun k => localAlpha_permSnake π q k, ?_⟩
  intro g hgm
  obtain ⟨ha, hb⟩ := hg g hgm
  let σ := Equiv.swap g.1 g.2
  have hmem : π.trans σ ∈ G := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c hc => ?_⟩
    show σ (π c) = c
    rw [hπ' c hc]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hc)) (fun h => hb (h ▸ hc))
  have hle := hmin _ hmem
  apply lex_of_key
  convert hle using 3
  funext v
  rw [Bool.eq_iff_iff, sel_iff, sel_iff]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    show (permV (π.trans σ) (q.vertex i)).val = v
    rw [permV_trans, permV_swap_val]
    show swapN g.1.val g.2.val ((permSnake π q).vertex i).val = v
    rw [hi, swapN_swapN]
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have : (permV (π.trans σ) (q.vertex i)).val = v := hi
    rw [permV_trans, permV_swap_val] at this
    show ((permSnake π q).vertex i).val = _
    rw [← this, swapN_swapN]
    rfl

end D239
