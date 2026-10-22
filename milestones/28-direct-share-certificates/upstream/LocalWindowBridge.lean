import LocalWindowModel
import PathStructure

/-!
# From a snake to the local window axioms

For a snake `p` and a window of consecutive path vertices, a cube automorphism
`φ(v) = π(v ⊕ t)` (translation by the first window vertex, then a permutation `π` of
the nine coordinates) moves the window onto one of the canonical windows of
`LocalWindowModel`.  The image of the snake's vertex set and endpoint set satisfies
`Axioms` for that canonical window, with centre counts equal to the snake's
singleton-square counts (`coreAlpha`).  Hence every certificate `Refuted window bounds`
excludes the corresponding count pattern on every internal window of every snake.

The main results are `no_certified_window_core` and `no_quad_window_core`, which
derive the window exclusions used by the conditional bounds 242 and 241 from
`AllRefuted`, the conjunction of the 22 certificate statements.
-/

namespace Snake9.LocalWindow
open Snake9

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! ## Generic list counting -/

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l l' : List α}, l.Nodup → (∀ x ∈ l, x ∈ l') → l.length ≤ l'.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l', hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ l' := hs a List.mem_cons_self
    have ih := nodup_length_le_of_subset (l' := l'.erase a) hn.2 (by
      intro x hx
      have hxa : x ≠ a := fun h => hn.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).2 (hs x (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem ha] at ih
    have : 0 < l'.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: t, hn, hi => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj hn.2 (fun x hx y hy =>
      hi x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    have := hi y (List.mem_cons_of_mem _ hy) a List.mem_cons_self he
    exact hn.1 (this ▸ hy)

/-- Counting through an injection: if `g` sends the `P`-entries of a duplicate-free
list injectively to `Q`-entries of `L'`, the first count is at most the second. -/
theorem filter_length_le {α β : Type} [DecidableEq β] (L : List α) (hL : L.Nodup)
    (L' : List β) (g : α → β) (hinj : ∀ x ∈ L, ∀ y ∈ L, g x = g y → x = y)
    (P : α → Bool) (Q : β → Bool)
    (hmem : ∀ x ∈ L, P x = true → g x ∈ L' ∧ Q (g x) = true) :
    (L.filter P).length ≤ (L'.filter Q).length := by
  have h1 : ((L.filter P).map g).Nodup :=
    nodup_map_of_inj (List.Pairwise.filter P hL) (fun x hx y hy =>
      hinj x (List.mem_filter.1 hx).1 y (List.mem_filter.1 hy).1)
  have h2 := nodup_length_le_of_subset h1 (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have hx' := List.mem_filter.1 hx
    exact List.mem_filter.2 (hmem x hx'.1 hx'.2))
  simpa using h2

/-- A duplicate-free list with two distinct members has length at least two. -/
theorem two_le_length_of_mem {α : Type} [DecidableEq α] {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : 2 ≤ l.length := by
  have h : [a, b].Nodup := by simp [hab]
  have := nodup_length_le_of_subset h (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
  simpa using this

/-! ## Bit permutations -/

/-- A permutation of the coordinates `0, …, 8`. -/
structure CPerm where
  fwd : Nat → Nat
  bwd : Nat → Nat
  fwd_lt : ∀ k, k < 9 → fwd k < 9
  bwd_lt : ∀ k, k < 9 → bwd k < 9
  bwd_fwd : ∀ k, k < 9 → bwd (fwd k) = k
  fwd_bwd : ∀ k, k < 9 → fwd (bwd k) = k

theorem CPerm.fwd_inj (P : CPerm) {a b : Nat} (ha : a < 9) (hb : b < 9)
    (h : P.fwd a = P.fwd b) : a = b := by
  rw [← P.bwd_fwd a ha, ← P.bwd_fwd b hb, h]

def bpermAux (τ : Nat → Nat) (v : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => bpermAux τ v j + (if v.testBit (τ j) then 2 ^ j else 0)

theorem bpermAux_lt (τ : Nat → Nat) (v : Nat) : ∀ n, bpermAux τ v n < 2 ^ n
  | 0 => by simp [bpermAux]
  | n + 1 => by
    have := bpermAux_lt τ v n
    simp only [bpermAux]
    rw [Nat.pow_succ]
    split <;> omega

theorem testBit_bpermAux (τ : Nat → Nat) (v : Nat) :
    ∀ n i, (bpermAux τ v n).testBit i = (decide (i < n) && v.testBit (τ i))
  | 0, i => by simp [bpermAux]
  | n + 1, i => by
    have ih := testBit_bpermAux τ v n i
    have hlt := bpermAux_lt τ v n
    simp only [bpermAux]
    by_cases hb : v.testBit (τ n) = true
    · rw [if_pos hb, Nat.add_comm]
      rcases Nat.lt_trichotomy i n with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]
        have h' : i < n + 1 := by omega
        simp [h, h']
      · subst h
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp [hb]
      · have : 2 ^ n + bpermAux τ v n < 2 ^ i := by
          have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) h
          rw [Nat.pow_succ] at this
          omega
        rw [Nat.testBit_lt_two_pow this]
        have h' : ¬ i < n + 1 := by omega
        simp [h']
    · rw [if_neg hb, Nat.add_zero]
      rcases Nat.lt_or_ge i n with h | h
      · rw [ih]
        have h' : i < n + 1 := by omega
        simp [h, h']
      · have : bpermAux τ v n < 2 ^ i :=
          Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) h)
        rw [Nat.testBit_lt_two_pow this]
        by_cases hi : i = n
        · subst hi
          simp at hb
          simp [hb]
        · have h' : ¬ i < n + 1 := by omega
          simp [h']

/-- The bit permutation sending coordinate `k` to `P.fwd k`. -/
def bperm (P : CPerm) (v : Nat) : Nat := bpermAux P.bwd v 9

theorem testBit_bperm (P : CPerm) (v i : Nat) :
    (bperm P v).testBit i = (decide (i < 9) && v.testBit (P.bwd i)) :=
  testBit_bpermAux _ _ 9 i

theorem bperm_lt (P : CPerm) (v : Nat) : bperm P v < 512 := bpermAux_lt _ _ 9

theorem bperm_xor (P : CPerm) (u w : Nat) : bperm P (u ^^^ w) = bperm P u ^^^ bperm P w := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [testBit_bperm, Nat.testBit_xor]
  cases decide (i < 9) <;> simp

theorem bperm_zero (P : CPerm) : bperm P 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [testBit_bperm]

theorem bperm_pow (P : CPerm) {k : Nat} (hk : k < 9) : bperm P (2 ^ k) = 2 ^ (P.fwd k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bperm, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases hi : i < 9
  · have : k = P.bwd i ↔ P.fwd k = i := by
      constructor
      · rintro rfl; exact P.fwd_bwd i hi
      · rintro rfl; exact (P.bwd_fwd k hk).symm
    simp [hi, this]
  · have : P.fwd k ≠ i := by have := P.fwd_lt k hk; omega
    simp [hi, this]

theorem testBit_of_lt_512 {u k : Nat} (hu : u < 512) (hk : ¬ k < 9) : u.testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have h9 : (2 : Nat) ^ 9 = 512 := by decide
  omega

theorem bperm_inj (P : CPerm) {u w : Nat} (hu : u < 512) (hw : w < 512)
    (h : bperm P u = bperm P w) : u = w := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 9
  · have := congrArg (fun z => Nat.testBit z (P.fwd k)) h
    simp only [testBit_bperm, P.fwd_lt k hk, P.bwd_fwd k hk, decide_true, Bool.true_and] at this
    exact this
  · rw [testBit_of_lt_512 hu hk, testBit_of_lt_512 hw hk]

/-- The cube automorphism `v ↦ π(v ⊕ t)`. -/
def amap (P : CPerm) (t v : Nat) : Nat := bperm P (v ^^^ t)

theorem amap_lt (P : CPerm) (t v : Nat) : amap P t v < 512 := bperm_lt _ _

theorem amap_flip (P : CPerm) (t v : Nat) {k : Nat} (hk : k < 9) :
    amap P t (v ^^^ 2 ^ k) = amap P t v ^^^ 2 ^ (P.fwd k) := by
  unfold amap
  rw [← bperm_pow P hk, ← bperm_xor, Nat.xor_assoc, Nat.xor_comm (2 ^ k) t, ← Nat.xor_assoc]

theorem amap_inj (P : CPerm) {t u w : Nat} (ht : t < 512) (hu : u < 512) (hw : w < 512)
    (h : amap P t u = amap P t w) : u = w := by
  have h512 : (512 : Nat) = 2 ^ 9 := by decide
  have hu' : u ^^^ t < 512 := by rw [h512] at *; exact Nat.xor_lt_two_pow hu ht
  have hw' : w ^^^ t < 512 := by rw [h512] at *; exact Nat.xor_lt_two_pow hw ht
  have := bperm_inj P hu' hw' h
  have := congrArg (· ^^^ t) this
  simpa [Nat.xor_assoc] using this

theorem amap_self (P : CPerm) (t : Nat) : amap P t t = 0 := by
  simp [amap, bperm_zero]

/-! ## Building coordinate permutations -/

def swapF (a b k : Nat) : Nat := if k = a then b else if k = b then a else k

theorem swapF_swapF (a b k : Nat) : swapF a b (swapF a b k) = k := by
  unfold swapF
  split <;> split <;> (try split) <;> omega

theorem swapF_lt {a b k : Nat} (ha : a < 9) (hb : b < 9) (hk : k < 9) : swapF a b k < 9 := by
  unfold swapF
  split
  · exact hb
  · split <;> omega

def CPerm.id : CPerm where
  fwd k := k
  bwd k := k
  fwd_lt _ h := h
  bwd_lt _ h := h
  bwd_fwd _ _ := rfl
  fwd_bwd _ _ := rfl

def CPerm.swapThen (P : CPerm) (a b : Nat) (ha : a < 9) (hb : b < 9) : CPerm where
  fwd k := swapF a b (P.fwd k)
  bwd k := P.bwd (swapF a b k)
  fwd_lt k hk := swapF_lt ha hb (P.fwd_lt k hk)
  bwd_lt k hk := P.bwd_lt _ (swapF_lt ha hb hk)
  bwd_fwd k hk := by simp only [swapF_swapF, P.bwd_fwd k hk]
  fwd_bwd k hk := by simp only [P.fwd_bwd _ (swapF_lt ha hb hk), swapF_swapF]

def CPerm.swap (P : CPerm) (a b : Nat) : CPerm :=
  if h : a < 9 ∧ b < 9 then P.swapThen a b h.1 h.2 else P

theorem CPerm.swap_fwd (P : CPerm) {a b : Nat} (ha : a < 9) (hb : b < 9) (k : Nat) :
    (P.swap a b).fwd k = swapF a b (P.fwd k) := by
  simp [CPerm.swap, ha, hb, CPerm.swapThen]

/-- Send the listed coordinates to `j, j+1, …` by successive transpositions. -/
def CPerm.build : CPerm → Nat → List Nat → CPerm
  | P, _, [] => P
  | P, j, d :: ds => CPerm.build (P.swap j (P.fwd d)) (j + 1) ds

theorem CPerm.build_spec : ∀ (ds : List Nat) (P : CPerm) (j : Nat), ds.Nodup →
    (∀ d ∈ ds, d < 9) → j + ds.length ≤ 9 → (∀ d ∈ ds, j ≤ P.fwd d) →
    (∀ x, x < 9 → P.fwd x < j → (CPerm.build P j ds).fwd x = P.fwd x) ∧
    (∀ i, i < ds.length → (CPerm.build P j ds).fwd (ds.getD i 0) = j + i)
  | [], P, j, _, _, _, _ => ⟨fun _ _ _ => rfl, fun i hi => by simp at hi⟩
  | d :: ds, P, j, hn, hlt, hlen, hge => by
    rw [List.nodup_cons] at hn
    simp only [List.length_cons] at hlen
    have hd : d < 9 := hlt d List.mem_cons_self
    have hj : j < 9 := by omega
    have hPd : P.fwd d < 9 := P.fwd_lt d hd
    have hjd : j ≤ P.fwd d := hge d List.mem_cons_self
    let Q := P.swap j (P.fwd d)
    have hQ : ∀ k, Q.fwd k = swapF j (P.fwd d) (P.fwd k) := CPerm.swap_fwd P hj hPd
    have hge' : ∀ d' ∈ ds, j + 1 ≤ Q.fwd d' := by
      intro d' hd'
      have hd'9 : d' < 9 := hlt d' (List.mem_cons_of_mem _ hd')
      have hne : P.fwd d' ≠ P.fwd d := by
        intro h
        have := P.fwd_inj hd'9 hd h
        exact hn.1 (this ▸ hd')
      have h1 : j ≤ P.fwd d' := hge d' (List.mem_cons_of_mem _ hd')
      rw [hQ]
      unfold swapF
      split <;> (try split) <;> omega
    obtain ⟨ih1, ih2⟩ := CPerm.build_spec ds Q (j + 1) hn.2
      (fun d' hd' => hlt d' (List.mem_cons_of_mem _ hd')) (by omega) hge'
    have hQd : Q.fwd d = j := by rw [hQ]; unfold swapF; split <;> (try split) <;> omega
    refine ⟨?_, ?_⟩
    · intro x hx hxj
      show (CPerm.build Q (j + 1) ds).fwd x = P.fwd x
      have hQx : Q.fwd x = P.fwd x := by
        rw [hQ]; unfold swapF; split <;> (try split) <;> omega
      rw [ih1 x hx (by omega), hQx]
    · intro i hi
      show (CPerm.build Q (j + 1) ds).fwd ((d :: ds).getD i 0) = j + i
      cases i with
      | zero =>
        simp only [List.getD_cons_zero]
        rw [ih1 d hd (by omega), hQd]; rfl
      | succ i =>
        simp only [List.getD_cons_succ]
        rw [ih2 i (by simp at hi; omega)]
        omega

/-- The coordinate permutation sending `ds[i]` to `i`. -/
def mkPerm (ds : List Nat) : CPerm := CPerm.build CPerm.id 0 ds

theorem mkPerm_spec {ds : List Nat} (hn : ds.Nodup) (hlt : ∀ d ∈ ds, d < 9)
    (hlen : ds.length ≤ 9) : ∀ i, i < ds.length → (mkPerm ds).fwd (ds.getD i 0) = i := by
  intro i hi
  have := (CPerm.build_spec ds CPerm.id 0 hn hlt (by omega) (fun _ _ => Nat.zero_le _)).2 i hi
  simpa using this

/-! ## Pair lists and neighbour lists -/

theorem freePairs_nodup : ∀ d₁, d₁ < 10 → ∀ d₂, d₂ < 10 → (freePairs d₁ d₂).Nodup := by decide

theorem mem_freePairs (a b d₁ d₂ : Nat) : (a, b) ∈ freePairs d₁ d₂ ↔
    a < b ∧ b < 9 ∧ a ≠ d₁ ∧ a ≠ d₂ ∧ b ≠ d₁ ∧ b ≠ d₂ := by
  simp only [freePairs, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    split at h
    · simp at h; obtain ⟨rfl, rfl⟩ := h; omega
    · simp at h
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨a, by omega, b, h2, by rw [if_pos ⟨h1, h3, h4, h5, h6⟩]⟩

theorem mem_nbrs (v w : Nat) : w ∈ nbrs v ↔ ∃ k, k < 9 ∧ w = v ^^^ 2 ^ k := by
  simp only [nbrs, List.mem_map, List.mem_range, Nat.one_shiftLeft]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

theorem pow_two_inj {a b : Nat} (h : 2 ^ a = 2 ^ b) : a = b := by
  have := congrArg Nat.log2 h
  simpa [Nat.log2_two_pow] using this

theorem xor_left_inj (v : Nat) {a b : Nat} (h : v ^^^ a = v ^^^ b) : a = b := by
  have := congrArg (v ^^^ ·) h
  simpa [← Nat.xor_assoc] using this

theorem nbrs_nodup (v : Nat) : (nbrs v).Nodup := by
  unfold nbrs
  apply nodup_map_of_inj List.nodup_range
  intro a _ b _ h
  apply pow_two_inj
  have := xor_left_inj v h
  simpa [Nat.one_shiftLeft] using this

theorem xor_pow_lt {v k : Nat} (hv : v < 512) (hk : k < 9) : v ^^^ 2 ^ k < 512 := by
  have h512 : (512 : Nat) = 2 ^ 9 := by decide
  rw [h512] at *
  exact Nat.xor_lt_two_pow hv (Nat.pow_lt_pow_of_lt (by omega) hk)

theorem dirOfStep_xor (a c : Nat) : dirOfStep a (a ^^^ 2 ^ c) = c := by
  unfold dirOfStep
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.log2_two_pow]

/-! ## Snakes on natural-number indices -/

/-- The `k`-th vertex of `p` as a natural number (zero beyond the end). -/
def vx {m : Nat} (p : Snake m) (k : Nat) : Nat :=
  if h : k < m + 1 then (p.vertex ⟨k, h⟩).val else 0

theorem vx_lt {m : Nat} (p : Snake m) (k : Nat) : vx p k < 512 := by
  unfold vx
  split
  · exact (p.vertex _).isLt
  · decide

theorem vx_inj {m : Nat} (p : Snake m) {i j : Nat} (hi : i ≤ m) (hj : j ≤ m)
    (h : vx p i = vx p j) : i = j := by
  unfold vx at h
  rw [dif_pos (by omega), dif_pos (by omega)] at h
  have := p.distinct _ _ (Fin.ext h)
  exact congrArg Fin.val this

theorem vx_adj_iff {m : Nat} (p : Snake m) {i j : Nat} (hi : i ≤ m) (hj : j ≤ m) :
    (∃ k, k < 9 ∧ vx p j = vx p i ^^^ 2 ^ k) ↔ (i + 1 = j ∨ j + 1 = i) := by
  have := path_adj_iff p ⟨i, by omega⟩ ⟨j, by omega⟩
  rw [adj_iff_coordinate_flip] at this
  unfold vx
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact this

/-- Direction of the path step from index `j` to `j+1`. -/
def dir {m : Nat} (p : Snake m) (j : Nat) : Nat := dirOfStep (vx p j) (vx p (j + 1))

theorem step_dir {m : Nat} (p : Snake m) {j : Nat} (hj : j < m) :
    dir p j < 9 ∧ vx p (j + 1) = vx p j ^^^ 2 ^ dir p j := by
  obtain ⟨k, hk, he⟩ := (vx_adj_iff p (i := j) (j := j + 1) (by omega) (by omega)).2 (Or.inl rfl)
  have hd : dir p j = k := by unfold dir; rw [he, dirOfStep_xor]
  rw [hd]
  exact ⟨hk, he⟩

theorem step_dir' {m : Nat} (p : Snake m) {j : Nat} (hj : j < m) :
    vx p j = vx p (j + 1) ^^^ 2 ^ dir p j := by
  rw [(step_dir p hj).2, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Image of the vertex set of `p` under `f`, as a Boolean predicate. -/
def sel {m : Nat} (p : Snake m) (f : Nat → Nat) (w : Nat) : Bool :=
  (List.range (m + 1)).any (fun i => f (vx p i) == w)

theorem sel_iff {m : Nat} (p : Snake m) (f : Nat → Nat) (w : Nat) :
    sel p f w = true ↔ ∃ i, i ≤ m ∧ f (vx p i) = w := by
  simp only [sel, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, by omega, h⟩

/-! ## Singleton-square counts -/

/-- The square at `c` spanned by coordinates `ab` has no selected vertex besides `c`. -/
def singPred (S : Nat → Bool) (c : Nat) (ab : Nat × Nat) : Bool :=
  !S (c ^^^ (1 <<< ab.1)) && !S (c ^^^ (1 <<< ab.2)) && !S (c ^^^ (1 <<< ab.1) ^^^ (1 <<< ab.2))

/-- Number of singleton squares at `c` over all 36 coordinate pairs. -/
def singCount (S : Nat → Bool) (c : Nat) : Nat := ((freePairs 9 9).filter (singPred S c)).length

/-- The singleton-square count of the snake at index `k` (identity frame). -/
def coreAlpha {m : Nat} (p : Snake m) (k : Nat) : Nat := singCount (sel p (fun v => v)) (vx p k)

theorem singPred_symm (S : Nat → Bool) (c a b : Nat) : singPred S c (b, a) = singPred S c (a, b) := by
  unfold singPred
  simp only
  rw [Nat.xor_assoc c (1 <<< b), Nat.xor_comm (1 <<< b), ← Nat.xor_assoc]
  cases S (c ^^^ (1 <<< a)) <;> cases S (c ^^^ (1 <<< b)) <;> simp

/-! ## The frame `φ(v) = π(v ⊕ t)` -/

section Frame
variable {m : Nat} (p : Snake m) (P : CPerm) (t : Nat)

theorem sel_amap (ht : t < 512) {u : Nat} (hu : u < 512) :
    sel p (amap P t) (amap P t u) = sel p (fun v => v) u := by
  apply Bool.eq_iff_iff.2
  rw [sel_iff, sel_iff]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, amap_inj P ht (vx_lt p i) hu h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rw [h]⟩

theorem singPred_sort (S : Nat → Bool) (c x y : Nat) :
    singPred S c (min x y, max x y) = singPred S c (x, y) := by
  by_cases h : x ≤ y
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), singPred_symm]

theorem singPred_frame (ht : t < 512) {c : Nat} (hc : c < 512) {a b : Nat} (ha : a < 9) (hb : b < 9) :
    singPred (sel p (amap P t)) (amap P t c) (P.fwd a, P.fwd b) =
      singPred (sel p (fun v => v)) c (a, b) := by
  unfold singPred
  simp only [Nat.one_shiftLeft]
  rw [← amap_flip P t c ha, ← amap_flip P t c hb, ← amap_flip P t _ hb,
    sel_amap p P t ht (xor_pow_lt hc ha), sel_amap p P t ht (xor_pow_lt hc hb),
    sel_amap p P t ht (xor_pow_lt (xor_pow_lt hc ha) hb)]

theorem singPred_frame_sorted (ht : t < 512) {c : Nat} (hc : c < 512) {a b : Nat} (ha : a < 9) (hb : b < 9) :
    singPred (sel p (amap P t)) (amap P t c) (min (P.fwd a) (P.fwd b), max (P.fwd a) (P.fwd b)) =
      singPred (sel p (fun v => v)) c (a, b) := by
  rw [← singPred_frame p P t ht hc ha hb]
  by_cases h : P.fwd a ≤ P.fwd b
  · rw [Nat.min_eq_left h, Nat.max_eq_right h]
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), singPred_symm]

theorem sorted_mem_inj (Q : CPerm) :
    ∀ x ∈ freePairs 9 9, ∀ y ∈ freePairs 9 9,
      (min (Q.fwd x.1) (Q.fwd x.2), max (Q.fwd x.1) (Q.fwd x.2)) =
        (min (Q.fwd y.1) (Q.fwd y.2), max (Q.fwd y.1) (Q.fwd y.2)) → x = y := by
  rintro ⟨a, b⟩ hx ⟨a', b'⟩ hy h
  rw [mem_freePairs] at hx hy
  simp only [Prod.mk.injEq] at h ⊢
  have hab : Q.fwd a ≠ Q.fwd b := fun e => by have := Q.fwd_inj (by omega) hx.2.1 e; omega
  have hab' : Q.fwd a' ≠ Q.fwd b' := fun e => by have := Q.fwd_inj (by omega) hy.2.1 e; omega
  have hc : (Q.fwd a = Q.fwd a' ∧ Q.fwd b = Q.fwd b') ∨ (Q.fwd a = Q.fwd b' ∧ Q.fwd b = Q.fwd a') := by
    obtain ⟨h1, h2⟩ := h
    by_cases e1 : Q.fwd a ≤ Q.fwd b <;> by_cases e2 : Q.fwd a' ≤ Q.fwd b'
    · rw [Nat.min_eq_left e1, Nat.max_eq_right e1, Nat.min_eq_left e2, Nat.max_eq_right e2] at *; omega
    · rw [Nat.min_eq_left e1, Nat.max_eq_right e1, Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)] at *; omega
    · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), Nat.min_eq_left e2, Nat.max_eq_right e2] at *; omega
    · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega), Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)] at *; omega
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Q.fwd_inj (by omega) (by omega) h1, Q.fwd_inj hx.2.1 hy.2.1 h2⟩
  · have e1 := Q.fwd_inj (by omega) hy.2.1 h1
    have e2 := Q.fwd_inj hx.2.1 (by omega) h2
    omega

theorem sorted_mem (Q : CPerm) : ∀ x ∈ freePairs 9 9,
    (min (Q.fwd x.1) (Q.fwd x.2), max (Q.fwd x.1) (Q.fwd x.2)) ∈ freePairs 9 9 := by
  rintro ⟨a, b⟩ hx
  rw [mem_freePairs] at hx ⊢
  have hab : Q.fwd a ≠ Q.fwd b := fun e => by have := Q.fwd_inj (by omega) hx.2.1 e; omega
  have h1 := Q.fwd_lt a (by omega)
  have h2 := Q.fwd_lt b hx.2.1
  simp only
  by_cases e1 : Q.fwd a ≤ Q.fwd b
  · rw [Nat.min_eq_left e1, Nat.max_eq_right e1]; omega
  · rw [Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)]; omega

/-- The inverse permutation. -/
def CPerm.inv (Q : CPerm) : CPerm where
  fwd := Q.bwd
  bwd := Q.fwd
  fwd_lt := Q.bwd_lt
  bwd_lt := Q.fwd_lt
  bwd_fwd := Q.fwd_bwd
  fwd_bwd := Q.bwd_fwd

/-- Singleton counts are invariant under the frame. -/
theorem singCount_frame (ht : t < 512) {c : Nat} (hc : c < 512) :
    singCount (sel p (amap P t)) (amap P t c) = singCount (sel p (fun v => v)) c := by
  unfold singCount
  apply Nat.le_antisymm
  · apply filter_length_le _ (freePairs_nodup 9 (by omega) 9 (by omega)) _ _
      (sorted_mem_inj P.inv)
    rintro ⟨a, b⟩ hx hs
    refine ⟨sorted_mem P.inv _ hx, ?_⟩
    have hx' := (mem_freePairs a b 9 9).1 hx
    simp only [CPerm.inv]
    rw [singPred_sort, ← singPred_frame p P t ht hc (P.bwd_lt a (by omega)) (P.bwd_lt b hx'.2.1),
      P.fwd_bwd a (by omega), P.fwd_bwd b hx'.2.1]
    exact hs
  · apply filter_length_le _ (freePairs_nodup 9 (by omega) 9 (by omega)) _ _
      (sorted_mem_inj P)
    rintro ⟨a, b⟩ hx hs
    refine ⟨sorted_mem P _ hx, ?_⟩
    have hx' := (mem_freePairs a b 9 9).1 hx
    rw [singPred_frame_sorted p P t ht hc (by omega) hx'.2.1]
    exact hs

theorem frame_nbr (ht : t < 512) {i w : Nat} (hi : i ≤ m) (hw : w ∈ nbrs (amap P t (vx p i)))
    (hs : sel p (amap P t) w = true) :
    ∃ j, j ≤ m ∧ w = amap P t (vx p j) ∧ (j + 1 = i ∨ i + 1 = j) := by
  obtain ⟨j, hj, rfl⟩ := (sel_iff _ _ _).1 hs
  obtain ⟨k, hk, he⟩ := (mem_nbrs _ _).1 hw
  refine ⟨j, hj, rfl, ?_⟩
  have hk' := P.bwd_lt k hk
  have : amap P t (vx p j) = amap P t (vx p i ^^^ 2 ^ P.bwd k) := by
    rw [amap_flip P t _ hk', P.fwd_bwd k hk]
    exact he
  have hv := amap_inj P ht (vx_lt p j) (xor_pow_lt (vx_lt p i) hk') this
  have := (vx_adj_iff p hi hj).1 ⟨P.bwd k, hk', hv⟩
  omega

theorem frame_nbr_mem {i j : Nat} (hi : i ≤ m) (hj : j ≤ m) (hadj : j + 1 = i ∨ i + 1 = j) :
    amap P t (vx p j) ∈ nbrs (amap P t (vx p i)) ∧ sel p (amap P t) (amap P t (vx p j)) = true := by
  obtain ⟨k, hk, he⟩ := (vx_adj_iff p hi hj).2 (by omega)
  refine ⟨?_, (sel_iff _ _ _).2 ⟨j, hj, rfl⟩⟩
  rw [mem_nbrs, he, amap_flip P t _ hk]
  exact ⟨_, P.fwd_lt k hk, rfl⟩

theorem frame_ne (ht : t < 512) {i j : Nat} (hi : i ≤ m) (hj : j ≤ m) (hij : i ≠ j) :
    amap P t (vx p i) ≠ amap P t (vx p j) := fun h =>
  hij (vx_inj p hi hj (amap_inj P ht (vx_lt p i) (vx_lt p j) h))

theorem frame_deg_le (ht : t < 512) {i : Nat} (hi : i ≤ m) :
    cnt (sel p (amap P t)) (nbrs (amap P t (vx p i))) ≤ 2 := by
  have h := nodup_length_le_of_subset (l' := [amap P t (vx p (i - 1)), amap P t (vx p (i + 1))])
    (List.Pairwise.filter (sel p (amap P t)) (nbrs_nodup (amap P t (vx p i)))) (by
      intro w hw
      rw [List.mem_filter] at hw
      obtain ⟨j, hj, rfl, hadj⟩ := frame_nbr p P t ht hi hw.1 hw.2
      rcases hadj with h | h
      · rw [show j = i - 1 by omega]; simp
      · rw [← h]; simp)
  simpa using h

theorem frame_deg_end (ht : t < 512) {i : Nat} (hi : i = 0 ∨ i = m) (hm : 1 ≤ m) :
    cnt (sel p (amap P t)) (nbrs (amap P t (vx p i))) ≤ 1 := by
  have h := nodup_length_le_of_subset (l' := [amap P t (vx p (if i = 0 then 1 else m - 1))])
    (List.Pairwise.filter (sel p (amap P t)) (nbrs_nodup (amap P t (vx p i)))) (by
      intro w hw
      rw [List.mem_filter] at hw
      obtain ⟨j, hj, rfl, hadj⟩ := frame_nbr p P t ht (by omega) hw.1 hw.2
      by_cases h0 : i = 0
      · rw [if_pos h0, show j = 1 by omega]; simp
      · rw [if_neg h0, show j = m - 1 by omega]; simp)
  simpa using h

theorem frame_deg_pos {i : Nat} (hi : i ≤ m) (hm : 1 ≤ m) :
    1 ≤ cnt (sel p (amap P t)) (nbrs (amap P t (vx p i))) := by
  have hj : ∃ j, j ≤ m ∧ (j + 1 = i ∨ i + 1 = j) := by
    by_cases h : i < m
    · exact ⟨i + 1, by omega, Or.inr rfl⟩
    · exact ⟨i - 1, by omega, Or.inl (by omega)⟩
  obtain ⟨j, hj, hadj⟩ := hj
  obtain ⟨h1, h2⟩ := frame_nbr_mem p P t hi hj hadj
  exact List.length_pos_of_mem (List.mem_filter.2 ⟨h1, h2⟩)

theorem frame_deg_internal (ht : t < 512) {i : Nat} (h0 : 0 < i) (hm : i < m) :
    2 ≤ cnt (sel p (amap P t)) (nbrs (amap P t (vx p i))) := by
  obtain ⟨a1, a2⟩ := frame_nbr_mem p P t (i := i) (j := i - 1) (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨b1, b2⟩ := frame_nbr_mem p P t (i := i) (j := i + 1) (by omega) (by omega) (Or.inr rfl)
  exact two_le_length_of_mem (List.mem_filter.2 ⟨a1, a2⟩) (List.mem_filter.2 ⟨b1, b2⟩)
    (frame_ne p P t ht (by omega) (by omega) (by omega))

/-- Selected neighbours of an internal vertex are exactly the two path neighbours. -/
theorem frame_internal_dirs (ht : t < 512) {k : Nat} (h0 : 0 < k) (hm : k < m) :
    let v := amap P t (vx p k)
    let S := sel p (amap P t)
    S (v ^^^ 2 ^ P.fwd (dir p (k - 1))) = true ∧ S (v ^^^ 2 ^ P.fwd (dir p k)) = true ∧
    ∀ a, a < 9 → S (v ^^^ 2 ^ a) = true → a = P.fwd (dir p (k - 1)) ∨ a = P.fwd (dir p k) := by
  intro v S
  have hl : amap P t (vx p (k - 1)) = v ^^^ 2 ^ P.fwd (dir p (k - 1)) := by
    have := step_dir' p (j := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at this
    rw [this, amap_flip P t _ (step_dir p (j := k - 1) (by omega)).1]
  have hr : amap P t (vx p (k + 1)) = v ^^^ 2 ^ P.fwd (dir p k) := by
    rw [(step_dir p hm).2, amap_flip P t _ (step_dir p hm).1]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hl]; exact (sel_iff _ _ _).2 ⟨k - 1, by omega, rfl⟩
  · rw [← hr]; exact (sel_iff _ _ _).2 ⟨k + 1, by omega, rfl⟩
  · intro a ha hs
    have hw : v ^^^ 2 ^ a ∈ nbrs v := (mem_nbrs _ _).2 ⟨a, ha, rfl⟩
    obtain ⟨j, hj, he, hadj⟩ := frame_nbr p P t ht (by omega) hw hs
    rcases hadj with h | h
    · rw [show j = k - 1 by omega, hl] at he
      exact Or.inl (pow_two_inj (xor_left_inj v he))
    · rw [← h, hr] at he
      exact Or.inr (pow_two_inj (xor_left_inj v he))

/-- At an internal vertex, the absent-corner count over free pairs is the singleton count. -/
theorem frame_absent_eq (ht : t < 512) {k : Nat} (h0 : 0 < k) (hm : k < m) :
    absentCorners (sel p (amap P t)) (amap P t (vx p k)) (P.fwd (dir p (k - 1))) (P.fwd (dir p k)) =
      singCount (sel p (amap P t)) (amap P t (vx p k)) := by
  obtain ⟨hs1, hs2, hsel⟩ := frame_internal_dirs p P t ht h0 hm
  have hd1 := P.fwd_lt _ (step_dir p (j := k - 1) (by omega)).1
  have hd2 := P.fwd_lt _ (step_dir p hm).1
  unfold absentCorners singCount
  apply Nat.le_antisymm
  · apply filter_length_le _ (freePairs_nodup _ (by omega) _ (by omega)) _ (fun x => x) (fun _ _ _ _ h => h)
    rintro ⟨a, b⟩ hx hs
    rw [mem_freePairs] at hx
    refine ⟨(mem_freePairs a b 9 9).2 ⟨hx.1, hx.2.1, by omega, by omega, by omega, by omega⟩, ?_⟩
    unfold singPred
    simp only [Nat.one_shiftLeft] at hs ⊢
    have ea : sel p (amap P t) (amap P t (vx p k) ^^^ 2 ^ a) = false := by
      cases e : sel p (amap P t) (amap P t (vx p k) ^^^ 2 ^ a)
      · rfl
      · rcases hsel a (by omega) e with h | h <;> omega
    have eb : sel p (amap P t) (amap P t (vx p k) ^^^ 2 ^ b) = false := by
      cases e : sel p (amap P t) (amap P t (vx p k) ^^^ 2 ^ b)
      · rfl
      · rcases hsel b hx.2.1 e with h | h <;> omega
    rw [ea, eb, hs]
    rfl
  · apply filter_length_le _ (freePairs_nodup 9 (by omega) 9 (by omega)) _ (fun x => x)
      (fun _ _ _ _ h => h)
    rintro ⟨a, b⟩ hx hs
    rw [mem_freePairs] at hx
    unfold singPred at hs
    simp only [Nat.one_shiftLeft, Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨⟨ha, hb⟩, hc⟩ := hs
    have na : a ≠ P.fwd (dir p (k - 1)) ∧ a ≠ P.fwd (dir p k) := by
      constructor <;> (rintro rfl; simp_all)
    have nb : b ≠ P.fwd (dir p (k - 1)) ∧ b ≠ P.fwd (dir p k) := by
      constructor <;> (rintro rfl; simp_all)
    refine ⟨(mem_freePairs a b _ _).2 ⟨hx.1, hx.2.1, na.1, na.2, nb.1, nb.2⟩, ?_⟩
    simp only [Nat.one_shiftLeft, hc]
    rfl

end Frame

/-! ## The identity frame -/

theorem bperm_id {v : Nat} (hv : v < 512) : bperm CPerm.id v = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bperm]
  by_cases hi : i < 9
  · simp [hi, CPerm.id]
  · simp [hi, testBit_of_lt_512 hv hi]

theorem amap_id {v : Nat} (hv : v < 512) : amap CPerm.id 0 v = v := by
  unfold amap
  rw [Nat.xor_zero, bperm_id hv]

theorem sel_amap_id {m : Nat} (p : Snake m) : sel p (amap CPerm.id 0) = sel p (fun v => v) := by
  funext w
  apply Bool.eq_iff_iff.2
  rw [sel_iff, sel_iff]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rw [← h, amap_id (vx_lt p i)]⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by rw [amap_id (vx_lt p i)]; exact h⟩

/-- At an internal vertex with path directions `dir p (k-1)` and `dir p k`, the
absent-corner count of the snake's own vertex set is its singleton count. -/
theorem absentCorners_eq_coreAlpha {m : Nat} (p : Snake m) {k : Nat} (h0 : 0 < k) (hm : k < m) :
    absentCorners (sel p (fun v => v)) (vx p k) (dir p (k - 1)) (dir p k) = coreAlpha p k := by
  have := frame_absent_eq p CPerm.id 0 (by decide) h0 hm
  rw [sel_amap_id, amap_id (vx_lt p k)] at this
  exact this

/-! ## Canonical windows -/

/-- `W` starts at `0` and follows the direction list `cs`. -/
structure Canon (W cs : List Nat) : Prop where
  len : W.length = cs.length + 1
  zero : W.getD 0 0 = 0
  step : ∀ j, j < cs.length → W.getD (j + 1) 0 = W.getD j 0 ^^^ 2 ^ (cs.getD j 0)

theorem canon_repeated : Canon winRepeated [0, 1, 2, 0] := ⟨rfl, rfl, by decide⟩
theorem canon_distinct : Canon winDistinct [0, 1, 2, 3] := ⟨rfl, rfl, by decide⟩
theorem canon_q01203 : Canon winQ01203 [0, 1, 2, 0, 3] := ⟨rfl, rfl, by decide⟩
theorem canon_q01230 : Canon winQ01230 [0, 1, 2, 3, 0] := ⟨rfl, rfl, by decide⟩
theorem canon_q01234 : Canon winQ01234 [0, 1, 2, 3, 4] := ⟨rfl, rfl, by decide⟩

theorem getD_of_mem {l : List Nat} {v : Nat} (h : v ∈ l) : ∃ j, j < l.length ∧ l.getD j 0 = v := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
  refine ⟨j, hj, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem two_mem_of_length {α : Type} {l : List α} (h : 2 ≤ l.length) (hn : l.Nodup) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  match l, h, hn with
  | a :: b :: _, _, hn =>
    refine ⟨a, b, List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    intro e
    rw [List.nodup_cons] at hn
    exact hn.1 (e ▸ List.mem_cons_self)

section Bridge
variable {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)

/-- The window vertices land on the canonical window. -/
theorem frame_window {W cs : List Nat} (hc : Canon W cs) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0) :
    ∀ j, j ≤ cs.length → W.getD j 0 = amap P (vx p r) (vx p (r + j)) := by
  intro j
  induction j with
  | zero => intro _; rw [hc.zero, Nat.add_zero, amap_self]
  | succ j ih =>
    intro hj
    obtain ⟨hd, he⟩ := step_dir p (j := r + j) (by omega)
    rw [hc.step j (by omega), ih (by omega), show r + (j + 1) = r + j + 1 from rfl, he,
      amap_flip P _ _ hd, hP j (by omega)]

/-- The endpoint set in the frame. -/
def frameE (t : Nat) (w : Nat) : Bool :=
  sel p (amap P t) w && (w == amap P t (vx p 0) || w == amap P t (vx p m))

theorem frameE_cases {t w : Nat} (h : frameE p P t w = true) :
    sel p (amap P t) w = true ∧ (w = amap P t (vx p 0) ∨ w = amap P t (vx p m)) := by
  unfold frameE at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h

/-- The image of a snake around a window satisfies the local window axioms. -/
theorem frame_axioms {W cs : List Nat} {bounds : List (Nat × Nat)} (hc : Canon W cs)
    (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) :
    Axioms (sel p (amap P (vx p r))) (frameE p P (vx p r)) W (centresOf W bounds) := by
  have ht : vx p r < 512 := vx_lt p r
  have hm : 1 ≤ m := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- window_sel
    intro v hv
    obtain ⟨j, hj, rfl⟩ := getD_of_mem hv
    rw [frame_window p P r hc hr hP j (by rw [hc.len] at hj; omega)]
    exact (sel_iff _ _ _).2 ⟨r + j, by rw [hc.len] at hj; omega, rfl⟩
  · -- sel_lt
    intro v hv
    obtain ⟨i, _, rfl⟩ := (sel_iff _ _ _).1 hv
    exact amap_lt _ _ _
  · -- deg_le_two
    intro v hv
    obtain ⟨i, hi, rfl⟩ := (sel_iff _ _ _).1 hv
    exact frame_deg_le p P _ ht hi
  · -- deg_pos
    intro v hv
    obtain ⟨i, hi, rfl⟩ := (sel_iff _ _ _).1 hv
    exact frame_deg_pos p P _ hi hm
  · -- acyclic
    intro C hne hdeg
    apply Classical.byContradiction
    intro hall
    have hall' : ∀ v ∈ C, sel p (amap P (vx p r)) v = true := by
      intro v hv
      cases e : sel p (amap P (vx p r)) v
      · exact absurd ⟨v, hv, e⟩ hall
      · rfl
    have ascent : ∀ n i, i ≤ m → m - i < n → amap P (vx p r) (vx p i) ∈ C → False := by
      intro n
      induction n with
      | zero => intro i _ h; omega
      | succ n ih =>
        intro i hi hlt hmem
        have hd := hdeg _ hmem
        obtain ⟨a, b, ha, hb, hab⟩ := two_mem_of_length hd
          (List.Pairwise.filter _ (nbrs_nodup _))
        rw [List.mem_filter] at ha hb
        have haC : a ∈ C := by simpa using ha.2
        have hbC : b ∈ C := by simpa using hb.2
        obtain ⟨ja, hja, rfl, hadja⟩ := frame_nbr p P _ ht hi ha.1 (hall' a haC)
        obtain ⟨jb, hjb, rfl, hadjb⟩ := frame_nbr p P _ ht hi hb.1 (hall' b hbC)
        rcases hadja with h1 | h1
        · rcases hadjb with h2 | h2
          · exact hab (by rw [show ja = jb by omega])
          · exact ih jb hjb (by omega) hbC
        · exact ih ja hja (by omega) haC
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil C hne
    obtain ⟨i, hi, rfl⟩ := (sel_iff _ _ _).1 (hall' v hv)
    exact ascent (m - i + 1) i hi (by omega) hv
  · -- end_sel
    intro v hv
    exact (frameE_cases p P hv).1
  · -- low_end
    intro v hv hc1
    obtain ⟨i, hi, rfl⟩ := (sel_iff _ _ _).1 hv
    have hend : i = 0 ∨ i = m := by
      apply Classical.byContradiction
      intro hn
      have := frame_deg_internal p P _ ht (i := i) (by omega) (by omega)
      omega
    unfold frameE
    rcases hend with rfl | rfl <;> simp [hv]
  · -- end_low
    intro v hv
    obtain ⟨hs, hv'⟩ := frameE_cases p P hv
    rcases hv' with rfl | rfl
    · exact frame_deg_end p P _ ht (Or.inl rfl) hm
    · exact frame_deg_end p P _ ht (Or.inr rfl) hm
  · -- end_two
    intro a b c ha hb hc'
    have ha' := (frameE_cases p P ha).2
    have hb' := (frameE_cases p P hb).2
    have hc'' := (frameE_cases p P hc').2
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> rcases hc'' with rfl | rfl <;> simp
  · -- alpha
    intro c hcen
    unfold centresOf at hcen
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hcen
    rw [List.mem_range] at hi
    show (bounds.getD i (0, 21)).1 ≤ absentCorners (sel p (amap P (vx p r))) (W.getD (i + 1) 0)
        (dirOfStep (W.getD i 0) (W.getD (i + 1) 0)) (dirOfStep (W.getD (i + 1) 0) (W.getD (i + 2) 0)) ∧
      absentCorners (sel p (amap P (vx p r))) (W.getD (i + 1) 0)
        (dirOfStep (W.getD i 0) (W.getD (i + 1) 0)) (dirOfStep (W.getD (i + 1) 0) (W.getD (i + 2) 0))
        ≤ (bounds.getD i (0, 21)).2
    have e1 : dirOfStep (W.getD i 0) (W.getD (i + 1) 0) = P.fwd (dir p (r + i)) := by
      rw [hc.step i (by omega), dirOfStep_xor, hP i (by omega)]
    have e2 : dirOfStep (W.getD (i + 1) 0) (W.getD (i + 2) 0) = P.fwd (dir p (r + i + 1)) := by
      rw [show i + 2 = i + 1 + 1 from rfl, hc.step (i + 1) (by omega), dirOfStep_xor]
      exact (hP (i + 1) (by omega)).symm
    have e3 : W.getD (i + 1) 0 = amap P (vx p r) (vx p (r + i + 1)) :=
      frame_window p P r hc hr hP (i + 1) (by omega)
    have key : absentCorners (sel p (amap P (vx p r))) (amap P (vx p r) (vx p (r + i + 1)))
        (P.fwd (dir p (r + i))) (P.fwd (dir p (r + i + 1))) = coreAlpha p (r + i + 1) := by
      have := frame_absent_eq p P (vx p r) ht (k := r + i + 1) (by omega) (by omega)
      rw [show r + i + 1 - 1 = r + i by omega] at this
      rw [this, singCount_frame p P _ ht (vx_lt p _)]
      rfl
    rw [e1, e2, e3, key]
    exact hb i hi

/-- A certificate for a canonical window excludes the count pattern on every window of a
snake whose directions are mapped onto the canonical ones by `P`. -/
theorem refuted_bridge {W cs : List Nat} {bounds : List (Nat × Nat)} (href : Refuted W bounds)
    (hc : Canon W cs) (hlen : bounds.length + 1 = cs.length) (hr : r + cs.length ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0)
    (hb : ∀ i, i < bounds.length → (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) : False :=
  href _ _ (frame_axioms p P r hc hlen hr hP hb)

end Bridge

/-! ## Reversal -/

def revSnake {m : Nat} (p : Snake m) : Snake m where
  vertex i := p.vertex ⟨m - i.val, by omega⟩
  distinct i j h := by
    have := congrArg Fin.val (p.distinct _ _ h)
    simp only at this
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by omega)
  induced i j hij := by
    rw [path_adj_iff]
    simp only
    have := i.isLt
    have := j.isLt
    omega

theorem vx_rev {m : Nat} (p : Snake m) {k : Nat} (hk : k ≤ m) : vx (revSnake p) k = vx p (m - k) := by
  unfold vx
  rw [dif_pos (by omega), dif_pos (by omega)]
  rfl

theorem sel_rev {m : Nat} (p : Snake m) : sel (revSnake p) (fun v => v) = sel p (fun v => v) := by
  funext w
  apply Bool.eq_iff_iff.2
  rw [sel_iff, sel_iff]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨m - i, by omega, by rw [← vx_rev p hi]; exact h⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨m - i, by omega, ?_⟩
    rw [vx_rev p (by omega), show m - (m - i) = i by omega]
    exact h

theorem coreAlpha_rev {m : Nat} (p : Snake m) {k : Nat} (hk : k ≤ m) :
    coreAlpha (revSnake p) k = coreAlpha p (m - k) := by
  unfold coreAlpha
  rw [sel_rev, vx_rev p hk]

theorem dir_rev {m : Nat} (p : Snake m) {j : Nat} (hj : j < m) :
    dir (revSnake p) j = dir p (m - j - 1) := by
  unfold dir
  rw [vx_rev p (by omega), vx_rev p (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
  rw [hk, show m - (j + 1) = k by omega, show k + 1 - 1 = k by omega]
  unfold dirOfStep
  rw [Nat.xor_comm]

/-! ## Direction constraints of induced paths -/

theorem xor_aa (x a : Nat) : x ^^^ a ^^^ a = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_aba (x a b : Nat) : x ^^^ a ^^^ b ^^^ a = x ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl

theorem xor_abcab (x a b c : Nat) : x ^^^ a ^^^ b ^^^ c ^^^ a ^^^ b = x ^^^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

section Dirs
variable {m : Nat} (p : Snake m)

theorem dir_lt {j : Nat} (hj : j < m) : dir p j < 9 := (step_dir p hj).1

theorem dir_ne_succ {j : Nat} (hj : j + 2 ≤ m) : dir p j ≠ dir p (j + 1) := by
  intro he
  have h1 : vx p (j + 1) = vx p j ^^^ 2 ^ dir p j := (step_dir p (j := j) (by omega)).2
  have h2 : vx p (j + 2) = vx p (j + 1) ^^^ 2 ^ dir p (j + 1) := (step_dir p (j := j + 1) (by omega)).2
  rw [h1, ← he, xor_aa] at h2
  have := vx_inj p (by omega) (by omega) h2
  omega

theorem dir_ne_two {j : Nat} (hj : j + 3 ≤ m) : dir p j ≠ dir p (j + 2) := by
  intro he
  have h1 : vx p (j + 1) = vx p j ^^^ 2 ^ dir p j := (step_dir p (j := j) (by omega)).2
  have h2 : vx p (j + 2) = vx p (j + 1) ^^^ 2 ^ dir p (j + 1) := (step_dir p (j := j + 1) (by omega)).2
  have h3 : vx p (j + 3) = vx p (j + 2) ^^^ 2 ^ dir p (j + 2) := (step_dir p (j := j + 2) (by omega)).2
  rw [h2, h1, ← he, xor_aba] at h3
  have := (vx_adj_iff p (i := j) (j := j + 3) (by omega) (by omega)).1
    ⟨_, dir_lt p (j := j + 1) (by omega), h3⟩
  omega

theorem dir_no_01201 {j : Nat} (hj : j + 5 ≤ m) :
    ¬(dir p (j + 3) = dir p j ∧ dir p (j + 4) = dir p (j + 1)) := by
  rintro ⟨he1, he2⟩
  have h1 : vx p (j + 1) = vx p j ^^^ 2 ^ dir p j := (step_dir p (j := j) (by omega)).2
  have h2 : vx p (j + 2) = vx p (j + 1) ^^^ 2 ^ dir p (j + 1) := (step_dir p (j := j + 1) (by omega)).2
  have h3 : vx p (j + 3) = vx p (j + 2) ^^^ 2 ^ dir p (j + 2) := (step_dir p (j := j + 2) (by omega)).2
  have h4 : vx p (j + 4) = vx p (j + 3) ^^^ 2 ^ dir p (j + 3) := (step_dir p (j := j + 3) (by omega)).2
  have h5 : vx p (j + 5) = vx p (j + 4) ^^^ 2 ^ dir p (j + 4) := (step_dir p (j := j + 4) (by omega)).2
  rw [h4, h3, h2, h1, he1, he2, xor_abcab] at h5
  have := (vx_adj_iff p (i := j) (j := j + 5) (by omega) (by omega)).1
    ⟨_, dir_lt p (j := j + 2) (by omega), h5⟩
  omega

end Dirs

/-! ## Selecting the certificate -/

theorem bounds_of3 {m : Nat} (p : Snake m) (r : Nat) {l0 h0 l1 h1 l2 h2 : Nat}
    (c0 : l0 ≤ coreAlpha p (r + 1) ∧ coreAlpha p (r + 1) ≤ h0)
    (c1 : l1 ≤ coreAlpha p (r + 2) ∧ coreAlpha p (r + 2) ≤ h1)
    (c2 : l2 ≤ coreAlpha p (r + 3) ∧ coreAlpha p (r + 3) ≤ h2) :
    ∀ i, i < [(l0, h0), (l1, h1), (l2, h2)].length →
      ([(l0, h0), (l1, h1), (l2, h2)].getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ ([(l0, h0), (l1, h1), (l2, h2)].getD i (0, 21)).2 := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · exact c0
  · exact c1
  · exact c2

theorem bounds_of4 {m : Nat} (p : Snake m) (r : Nat) {l0 h0 l1 h1 l2 h2 l3 h3 : Nat}
    (c0 : l0 ≤ coreAlpha p (r + 1) ∧ coreAlpha p (r + 1) ≤ h0)
    (c1 : l1 ≤ coreAlpha p (r + 2) ∧ coreAlpha p (r + 2) ≤ h1)
    (c2 : l2 ≤ coreAlpha p (r + 3) ∧ coreAlpha p (r + 3) ≤ h2)
    (c3 : l3 ≤ coreAlpha p (r + 4) ∧ coreAlpha p (r + 4) ≤ h3) :
    ∀ i, i < [(l0, h0), (l1, h1), (l2, h2), (l3, h3)].length →
      ([(l0, h0), (l1, h1), (l2, h2), (l3, h3)].getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ ([(l0, h0), (l1, h1), (l2, h2), (l3, h3)].getD i (0, 21)).2 := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · exact c0
  · exact c1
  · exact c2
  · exact c3

/-- Both triple shapes are covered by the repeated and distinct certificates. -/
theorem triple_core {l0 h0 l1 h1 l2 h2 : Nat}
    (hR : Refuted winRepeated [(l0, h0), (l1, h1), (l2, h2)])
    (hD : Refuted winDistinct [(l0, h0), (l1, h1), (l2, h2)])
    {m : Nat} (p : Snake m) (r : Nat) (hr : r + 4 ≤ m)
    (c0 : l0 ≤ coreAlpha p (r + 1) ∧ coreAlpha p (r + 1) ≤ h0)
    (c1 : l1 ≤ coreAlpha p (r + 2) ∧ coreAlpha p (r + 2) ≤ h1)
    (c2 : l2 ≤ coreAlpha p (r + 3) ∧ coreAlpha p (r + 3) ≤ h2) : False := by
  have hb := bounds_of3 p r c0 c1 c2
  have la := dir_lt p (j := r) (by omega)
  have lb := dir_lt p (j := r + 1) (by omega)
  have lc := dir_lt p (j := r + 2) (by omega)
  have le := dir_lt p (j := r + 3) (by omega)
  have n1 : dir p r ≠ dir p (r + 1) := dir_ne_succ p (j := r) (by omega)
  have n2 : dir p (r + 1) ≠ dir p (r + 2) := dir_ne_succ p (j := r + 1) (by omega)
  have n3 : dir p (r + 2) ≠ dir p (r + 3) := dir_ne_succ p (j := r + 2) (by omega)
  have n4 : dir p r ≠ dir p (r + 2) := dir_ne_two p (j := r) (by omega)
  have n5 : dir p (r + 1) ≠ dir p (r + 3) := dir_ne_two p (j := r + 1) (by omega)
  by_cases he : dir p (r + 3) = dir p r
  · have hsp := mkPerm_spec (ds := [dir p r, dir p (r + 1), dir p (r + 2)])
      (by simp [List.nodup_cons]; omega) (by simp; omega) (by simp)
    apply refuted_bridge p (mkPerm [dir p r, dir p (r + 1), dir p (r + 2)]) r hR canon_repeated
      rfl (by simp; omega) _ hb
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · simpa using hsp 0 (by simp)
    · simpa using hsp 1 (by simp)
    · simpa using hsp 2 (by simp)
    · rw [he]; simpa using hsp 0 (by simp)
  · have hsp := mkPerm_spec (ds := [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 3)])
      (by simp [List.nodup_cons]; omega) (by simp; omega) (by simp)
    apply refuted_bridge p (mkPerm [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 3)]) r hD
      canon_distinct rfl (by simp; omega) _ hb
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · simpa using hsp 0 (by simp)
    · simpa using hsp 1 (by simp)
    · simpa using hsp 2 (by simp)
    · simpa using hsp 3 (by simp)

/-- Quadruple shape `0,1,2,0,3`. -/
theorem quad_01203 {l0 h0 l1 h1 l2 h2 l3 h3 : Nat}
    (h : Refuted winQ01203 [(l0, h0), (l1, h1), (l2, h2), (l3, h3)])
    {m : Nat} (p : Snake m) (r : Nat) (hr : r + 5 ≤ m) (he : dir p (r + 3) = dir p r)
    (c0 : l0 ≤ coreAlpha p (r + 1) ∧ coreAlpha p (r + 1) ≤ h0)
    (c1 : l1 ≤ coreAlpha p (r + 2) ∧ coreAlpha p (r + 2) ≤ h1)
    (c2 : l2 ≤ coreAlpha p (r + 3) ∧ coreAlpha p (r + 3) ≤ h2)
    (c3 : l3 ≤ coreAlpha p (r + 4) ∧ coreAlpha p (r + 4) ≤ h3) : False := by
  have hb := bounds_of4 p r c0 c1 c2 c3
  have la := dir_lt p (j := r) (by omega)
  have lb := dir_lt p (j := r + 1) (by omega)
  have lc := dir_lt p (j := r + 2) (by omega)
  have lg := dir_lt p (j := r + 4) (by omega)
  have n1 : dir p r ≠ dir p (r + 1) := dir_ne_succ p (j := r) (by omega)
  have n2 : dir p (r + 1) ≠ dir p (r + 2) := dir_ne_succ p (j := r + 1) (by omega)
  have n4 : dir p (r + 3) ≠ dir p (r + 4) := dir_ne_succ p (j := r + 3) (by omega)
  have n5 : dir p r ≠ dir p (r + 2) := dir_ne_two p (j := r) (by omega)
  have n7 : dir p (r + 2) ≠ dir p (r + 4) := dir_ne_two p (j := r + 2) (by omega)
  have n8 := dir_no_01201 p (j := r) (by omega)
  have hgb : dir p (r + 4) ≠ dir p (r + 1) := fun e => n8 ⟨he, e⟩
  have hsp := mkPerm_spec (ds := [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 4)])
    (by simp [List.nodup_cons]; omega) (by simp; omega) (by simp)
  apply refuted_bridge p (mkPerm [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 4)]) r h
    canon_q01203 rfl (by simp; omega) _ hb
  intro j hj
  simp only [List.length_cons, List.length_nil] at hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · simpa using hsp 0 (by simp)
  · simpa using hsp 1 (by simp)
  · simpa using hsp 2 (by simp)
  · rw [he]; simpa using hsp 0 (by simp)
  · simpa using hsp 3 (by simp)

/-- All quadruple shapes; shape `0,1,2,3,1` is read backwards as `0,1,2,0,3`. -/
theorem quad_core {l0 h0 l1 h1 l2 h2 l3 h3 : Nat}
    (hA : Refuted winQ01203 [(l0, h0), (l1, h1), (l2, h2), (l3, h3)])
    (hB : Refuted winQ01230 [(l0, h0), (l1, h1), (l2, h2), (l3, h3)])
    (hC : Refuted winQ01234 [(l0, h0), (l1, h1), (l2, h2), (l3, h3)])
    (hD : Refuted winQ01203 [(l3, h3), (l2, h2), (l1, h1), (l0, h0)])
    {m : Nat} (p : Snake m) (r : Nat) (hr : r + 5 ≤ m)
    (c0 : l0 ≤ coreAlpha p (r + 1) ∧ coreAlpha p (r + 1) ≤ h0)
    (c1 : l1 ≤ coreAlpha p (r + 2) ∧ coreAlpha p (r + 2) ≤ h1)
    (c2 : l2 ≤ coreAlpha p (r + 3) ∧ coreAlpha p (r + 3) ≤ h2)
    (c3 : l3 ≤ coreAlpha p (r + 4) ∧ coreAlpha p (r + 4) ≤ h3) : False := by
  by_cases he : dir p (r + 3) = dir p r
  · exact quad_01203 hA p r hr he c0 c1 c2 c3
  have la := dir_lt p (j := r) (by omega)
  have lb := dir_lt p (j := r + 1) (by omega)
  have lc := dir_lt p (j := r + 2) (by omega)
  have le := dir_lt p (j := r + 3) (by omega)
  have lg := dir_lt p (j := r + 4) (by omega)
  have n1 : dir p r ≠ dir p (r + 1) := dir_ne_succ p (j := r) (by omega)
  have n2 : dir p (r + 1) ≠ dir p (r + 2) := dir_ne_succ p (j := r + 1) (by omega)
  have n3 : dir p (r + 2) ≠ dir p (r + 3) := dir_ne_succ p (j := r + 2) (by omega)
  have n4 : dir p (r + 3) ≠ dir p (r + 4) := dir_ne_succ p (j := r + 3) (by omega)
  have n5 : dir p r ≠ dir p (r + 2) := dir_ne_two p (j := r) (by omega)
  have n6 : dir p (r + 1) ≠ dir p (r + 3) := dir_ne_two p (j := r + 1) (by omega)
  have n7 : dir p (r + 2) ≠ dir p (r + 4) := dir_ne_two p (j := r + 2) (by omega)
  by_cases hgb : dir p (r + 4) = dir p (r + 1)
  · -- read the window backwards
    let q := revSnake p
    let r' := m - r - 5
    have hq : r' + 3 ≤ m := by omega
    have hdq : dir q (r' + 3) = dir q r' := by
      rw [dir_rev p (by omega), dir_rev p (by omega), show m - (r' + 3) - 1 = r + 1 by omega,
        show m - r' - 1 = r + 4 by omega, hgb]
    have ca : ∀ i, i < 4 → coreAlpha q (r' + i + 1) = coreAlpha p (r + 4 - i) := by
      intro i hi
      rw [coreAlpha_rev p (by omega), show m - (r' + i + 1) = r + 4 - i by omega]
    have d0 := ca 0 (by omega)
    have d1 := ca 1 (by omega)
    have d2 := ca 2 (by omega)
    have d3 := ca 3 (by omega)
    simp only [Nat.add_zero, Nat.sub_zero] at d0 d1 d2 d3
    rw [show r + 4 - 1 = r + 3 by omega] at d1
    rw [show r + 4 - 2 = r + 2 by omega] at d2
    rw [show r + 4 - 3 = r + 1 by omega] at d3
    exact quad_01203 hD q r' (by omega) hdq
      (by rw [d0]; exact c3) (by rw [d1]; exact c2) (by rw [d2]; exact c1) (by rw [d3]; exact c0)
  have hb := bounds_of4 p r c0 c1 c2 c3
  by_cases hga : dir p (r + 4) = dir p r
  · have hsp := mkPerm_spec (ds := [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 3)])
      (by simp [List.nodup_cons]; omega) (by simp; omega) (by simp)
    apply refuted_bridge p (mkPerm [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 3)]) r hB
      canon_q01230 rfl (by simp; omega) _ hb
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · simpa using hsp 0 (by simp)
    · simpa using hsp 1 (by simp)
    · simpa using hsp 2 (by simp)
    · simpa using hsp 3 (by simp)
    · rw [hga]; simpa using hsp 0 (by simp)
  · have hsp := mkPerm_spec
      (ds := [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 3), dir p (r + 4)])
      (by simp [List.nodup_cons]; omega) (by simp; omega) (by simp)
    apply refuted_bridge p
      (mkPerm [dir p r, dir p (r + 1), dir p (r + 2), dir p (r + 3), dir p (r + 4)]) r hC
      canon_q01234 rfl (by simp; omega) _ hb
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · simpa using hsp 0 (by simp)
    · simpa using hsp 1 (by simp)
    · simpa using hsp 2 (by simp)
    · simpa using hsp 3 (by simp)
    · simpa using hsp 4 (by simp)

/-! ## The 22 certificates and the window exclusions -/

/-- The 22 certificate statements of `milestones/10-window-aggregate/data/lean_core/`. -/
def AllRefuted : Prop :=
  -- 223_fwd_distinct, 223_fwd_repeated, 223_rev_distinct, 223_rev_repeated
  Refuted winDistinct [(2, 2), (2, 2), (3, 3)] ∧ Refuted winRepeated [(2, 2), (2, 2), (3, 3)] ∧
  Refuted winDistinct [(3, 3), (2, 2), (2, 2)] ∧ Refuted winRepeated [(3, 3), (2, 2), (2, 2)] ∧
  -- 224_fwd_distinct, 224_fwd_repeated, 224_rev_distinct, 224_rev_repeated
  Refuted winDistinct [(2, 2), (2, 2), (4, 4)] ∧ Refuted winRepeated [(2, 2), (2, 2), (4, 4)] ∧
  Refuted winDistinct [(4, 4), (2, 2), (2, 2)] ∧ Refuted winRepeated [(4, 4), (2, 2), (2, 2)] ∧
  -- 232_fwd_distinct, 232_fwd_repeated, 323_fwd_distinct, 323_fwd_repeated
  Refuted winDistinct [(2, 2), (3, 3), (2, 2)] ∧ Refuted winRepeated [(2, 2), (3, 3), (2, 2)] ∧
  Refuted winDistinct [(3, 3), (2, 2), (3, 3)] ∧ Refuted winRepeated [(3, 3), (2, 2), (3, 3)] ∧
  -- 41c_fwd_distinct, 41c_fwd_repeated, 41c_rev_distinct, 41c_rev_repeated
  Refuted winDistinct [(4, 4), (1, 1), (4, 6)] ∧ Refuted winRepeated [(4, 4), (1, 1), (4, 6)] ∧
  Refuted winDistinct [(4, 6), (1, 1), (4, 4)] ∧ Refuted winRepeated [(4, 6), (1, 1), (4, 4)] ∧
  -- 2423_fwd_s01203, 2423_fwd_s01230, 2423_fwd_s01234
  Refuted winQ01203 [(2, 2), (4, 4), (2, 2), (3, 3)] ∧
  Refuted winQ01230 [(2, 2), (4, 4), (2, 2), (3, 3)] ∧
  Refuted winQ01234 [(2, 2), (4, 4), (2, 2), (3, 3)] ∧
  -- 2423_rev_s01203, 2423_rev_s01230, 2423_rev_s01234
  Refuted winQ01203 [(3, 3), (2, 2), (4, 4), (2, 2)] ∧
  Refuted winQ01230 [(3, 3), (2, 2), (4, 4), (2, 2)] ∧
  Refuted winQ01234 [(3, 3), (2, 2), (4, 4), (2, 2)]

/-- The certified triple patterns (`WindowAggregate.Certified`, restated in core). -/
def CertPattern (x y z : Nat) : Prop :=
  ((x = 2 ∧ y = 2 ∧ 2 ≤ z ∧ z ≤ 4) ∨ (z = 2 ∧ y = 2 ∧ 2 ≤ x ∧ x ≤ 4) ∨
    (x = 2 ∧ y = 3 ∧ z = 2) ∨ (x = 3 ∧ y = 2 ∧ z = 3) ∨
    (x = 4 ∧ y = 1 ∧ 4 ≤ z ∧ z ≤ 6) ∨ (z = 4 ∧ y = 1 ∧ 4 ≤ x ∧ x ≤ 6)) ∧
  ¬(x = 2 ∧ y = 2 ∧ z = 2)

/-- The certified quadruple patterns (`WindowAggregate.QuadExcluded`, restated in core). -/
def QuadPattern (x y z w : Nat) : Prop :=
  (x = 2 ∧ y = 4 ∧ z = 2 ∧ w = 3) ∨ (x = 3 ∧ y = 2 ∧ z = 4 ∧ w = 2)

theorem no_certified_window_core (h : AllRefuted) {m : Nat} (p : Snake m) (r : Nat)
    (hr : r + 4 ≤ m) :
    ¬CertPattern (coreAlpha p (r + 1)) (coreAlpha p (r + 2)) (coreAlpha p (r + 3)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, -⟩ := h
  rintro ⟨hc, hn⟩
  rcases hc with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ |
    ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
  · rcases (show coreAlpha p (r + 3) = 3 ∨ coreAlpha p (r + 3) = 4 by omega) with e | e
    · exact triple_core a2 a1 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    · exact triple_core a6 a5 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · rcases (show coreAlpha p (r + 1) = 3 ∨ coreAlpha p (r + 1) = 4 by omega) with e | e
    · exact triple_core a4 a3 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    · exact triple_core a8 a7 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact triple_core a10 a9 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact triple_core a12 a11 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact triple_core a14 a13 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact triple_core a16 a15 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

theorem no_quad_window_core (h : AllRefuted) {m : Nat} (p : Snake m) (r : Nat)
    (hr : r + 5 ≤ m) :
    ¬QuadPattern (coreAlpha p (r + 1)) (coreAlpha p (r + 2)) (coreAlpha p (r + 3))
      (coreAlpha p (r + 4)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, b1, b2, b3, b4, b5, b6⟩ := h
  rintro (⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩)
  · exact quad_core b1 b2 b3 b4 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · exact quad_core b4 b5 b6 b1 p r hr ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

#print axioms no_certified_window_core
#print axioms no_quad_window_core

end Snake9.LocalWindow
