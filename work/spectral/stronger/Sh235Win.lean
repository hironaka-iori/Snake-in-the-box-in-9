import Sh235G1
/-!
# Windows of a shape CNF: from a snake to a contradiction

A canonical direction list `c` (shape) spans the window `wv c 0 = 0`,
`wv c (i+1) = wv c i xor 2^(c[i])`; its centres are `wv c i` for `1 ≤ i < c.length`, with
path directions `c[i-1]`, `c[i]`.  `WinRef c rs`: no snake runs through the window (positions
`r .. r + c.length`) with centre counts in the ranges `rs` (`InR`, an upper bound `≥ 21` means
none).

`winRef_of` derives `WinRef c rs` from
* the shape CNF data `D` and the used clauses `F`, all accepted by `check3` (G1, checked once per
  shape), with the window units, the lex generators of the free coordinates and, for every
  centre, a totalizer root node whose leaves are the negated 21 free corners (`cenOK`);
* a clause `C` with `F ⊨ C` (G2, e.g. a FastRup target) all of whose literals contradict the
  ranges (`litOff`): `C` is `¬core` for a core of the window's cube `o_lo, ¬o_(hi+1)`.
-/
namespace S235
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1 D239

/-- Count range: `lo ≤ a ≤ hi`, an upper bound `hi ≥ 21` meaning none. -/
def InR (lo hi a : Nat) : Prop := lo ≤ a ∧ (a ≤ hi ∨ 21 ≤ hi)

def wv (c : List Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => wv c i ^^^ 2 ^ c.getD i 0

def winL (c : List Nat) : List Nat := (List.range (c.length + 1)).map (wv c)

def coordOf (n : Nat) : Coord := ⟨n % 9, Nat.mod_lt _ (by decide)⟩

/-- Centres: (root node, vertex, incoming direction, outgoing direction). -/
def cenOf (c roots : List Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range (c.length - 1)).map fun i => (roots.getD i 0, wv c (i + 1), c.getD i 0, c.getD (i + 1) 0)

def cenOK (D : Sh) (t : Nat × Nat × Nat × Nat) : Bool :=
  (nodeL D.Tot t.1).all (negBall D.T) &&
    (nodeL D.Tot t.1).map (litV D.T) == cornerVerts t.2.1 t.2.2.1 t.2.2.2

def specOf (roots : List Nat) (rs : List (Nat × Nat)) : List (Nat × Nat × Nat) :=
  (List.range rs.length).map fun i => (roots.getD i 0, (rs.getD i (0, 0)).1, (rs.getD i (0, 0)).2)

/-- A literal of the target clause that the count ranges make false. -/
def litOff (D : Sh) (spec : List (Nat × Nat × Nat)) : Lit → Bool
  | .ofNat v => inTot D v && match totDec v 0 D.Tot with
      | some (n, j) => spec.any fun t => t.1 == n && decide (t.2.2 < j) && decide (t.2.2 < 21)
      | none => false
  | .negSucc v => inTot D (v + 1) && match totDec (v + 1) 0 D.Tot with
      | some (n, j) => spec.any fun t => t.1 == n && decide (j ≤ t.2.1)
      | none => false

/-- Vertex value at a position (`0` past the end), and the snake through the window `c`. -/
def vtx {m : Nat} (q : Snake m) (n : Nat) : Nat := if h : n ≤ m then (q.vertex ⟨n, by omega⟩).val else 0

def WinRef (c : List Nat) (rs : List (Nat × Nat)) : Prop :=
  ∀ {m : Nat} (q : Snake m) (r : Nat), r + c.length ≤ m → (∀ i ≤ c.length, vtx q (r + i) = wv c i) →
    (∀ i < rs.length, InR (rs.getD i (0, 0)).1 (rs.getD i (0, 0)).2 (countSeq q (r + i + 1))) → False

/-- Range tuples in compact form: base-8 digits, least significant first; digit `d < 6` is the
exact count `d`, digit `6` the lumped range `[6, 21]`. -/
def rng (d : Nat) : Nat × Nat := if d = 6 then (6, 21) else (d, d)

def decR : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | k + 1, z => rng (z % 8) :: decR k (z / 8)

def ShapeRefuted (c : List Nat) (L : List (List (Nat × Nat))) : Prop := ∀ rs ∈ L, WinRef c rs

theorem shapeRefuted_nil (c : List Nat) : ShapeRefuted c [] := fun _ h => absurd h List.not_mem_nil

theorem shapeRefuted_cons {c : List Nat} {rs : List (Nat × Nat)} {L : List (List (Nat × Nat))}
    (h : WinRef c rs) (t : ShapeRefuted c L) : ShapeRefuted c (rs :: L) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact t x hx

/-! ### Cube literals -/

theorem litOff_false {D : Sh} {S : Nat → Bool} {spec : List (Nat × Nat × Nat)}
    (hs : ∀ t ∈ spec, InR t.2.1 t.2.2 (cnt (baseVal D.T S) (nodeL D.Tot t.1)))
    {l : Lit} (h : litOff D spec l = true) : litSat (tau3 D S) l = false := by
  match l, h with
  | .ofNat v, h =>
    simp only [litOff, Bool.and_eq_true] at h
    obtain ⟨hin, h⟩ := h
    split at h
    · rename_i n j hd
      obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      obtain ⟨⟨rfl, h1⟩, h2⟩ := hm
      have := hs t ht
      show tau3 D S v = false
      unfold tau3; rw [if_pos hin, hd]
      unfold InR at this
      simp only [decide_eq_false_iff_not]; omega
    · exact absurd h (by simp)
  | .negSucc v, h =>
    simp only [litOff, Bool.and_eq_true] at h
    obtain ⟨hin, h⟩ := h
    split at h
    · rename_i n j hd
      obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
      obtain ⟨rfl, h1⟩ := hm
      have := hs t ht
      show (!tau3 D S (v + 1)) = false
      unfold tau3; rw [if_pos hin, hd]
      unfold InR at this
      simp only [Bool.not_eq_false', decide_eq_true_eq]; omega
    · exact absurd h (by simp)

theorem cube_false {D : Sh} {S : Nat → Bool} {spec : List (Nat × Nat × Nat)} {C : Clause}
    (hs : ∀ t ∈ spec, InR t.2.1 t.2.2 (cnt (baseVal D.T S) (nodeL D.Tot t.1)))
    (hc : C.all (litOff D spec) = true) (hC : clauseSat (tau3 D S) C) : False := by
  obtain ⟨l, hl, hsat⟩ := (clauseSat_iff _ C).mp hC
  rw [litOff_false hs (List.all_eq_true.mp hc l hl)] at hsat
  exact Bool.false_ne_true hsat

/-! ### Window geometry -/

theorem testBit_wv (c : List Nat) : ∀ (i j : Nat), (wv c i).testBit j = true →
    ∃ k < i, c.getD k 0 = j
  | 0, j, h => by simp [wv] at h
  | i + 1, j, h => by
    simp only [wv, Nat.testBit_xor, Nat.testBit_two_pow] at h
    by_cases hj : c.getD i 0 = j
    · exact ⟨i, by omega, hj⟩
    · rw [decide_eq_false hj, Bool.xor_false] at h
      obtain ⟨k, hk, he⟩ := testBit_wv c i j h
      exact ⟨k, by omega, he⟩

theorem getD_mem (c : List Nat) (k : Nat) (hk : k < c.length) : c.getD k 0 ∈ c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact List.getElem_mem hk

theorem bitsIn_wv (c : List Nat) (h9 : c.all (· < 9) = true) (i : Nat) (hi : i ≤ c.length)
    (v : Vertex) (hv : v.val = wv c i) : BitsIn (c.map coordOf) v := by
  intro a ha
  rw [hv] at ha
  obtain ⟨k, hk, he⟩ := testBit_wv c i a.val ha
  have hm := getD_mem c k (by omega)
  have h9' := List.all_eq_true.mp h9 _ hm
  simp only [decide_eq_true_eq] at h9'
  refine List.mem_map.mpr ⟨c.getD k 0, hm, ?_⟩
  apply Fin.ext; simp only [coordOf]; rw [he]; exact Nat.mod_eq_of_lt a.isLt

theorem wv_lt (c : List Nat) (h9 : c.all (· < 9) = true) : ∀ i, i ≤ c.length → wv c i < 512
  | 0, _ => by simp [wv]
  | i + 1, hi => by
    have hm := getD_mem c i (by omega)
    have h9' := List.all_eq_true.mp h9 _ hm
    simp only [decide_eq_true_eq] at h9'
    have h1 := wv_lt c h9 i (by omega)
    have h2 : 2 ^ c.getD i 0 < 2 ^ 9 := Nat.pow_lt_pow_right (by decide) h9'
    simp only [wv]
    exact Nat.xor_lt_two_pow (n := 9) h1 h2

/-! ### Centres -/

section
variable {m : Nat}

theorem vtx_eq (q : Snake m) {n : Nat} (hn : n ≤ m) : vtx q n = (q.vertex ⟨n, by omega⟩).val := by
  unfold vtx; rw [dif_pos hn]

/-- The free-corner count at an internal position `p` whose window neighbours differ in
coordinates `a` (before) and `b` (after). -/
theorem centreW (q : Snake m) (p : Nat) (hp1 : 1 ≤ p) (hpm : p + 1 ≤ m) (x a b : Nat)
    (ha : a < 9) (hb : b < 9) (hx : vtx q p = x) (hprev : vtx q (p - 1) = x ^^^ 2 ^ a)
    (hnext : vtx q (p + 1) = x ^^^ 2 ^ b)
    (hco : CornerOK x (coordOf a) (coordOf b) (cornerVerts x a b)) :
    ((cornerVerts x a b).filter (fun y => !sel q y)).length = countSeq q p := by
  obtain ⟨e1, e2, e3, e4⟩ := hco
  rw [vtx_eq q (by omega)] at hx hprev hnext
  have hc : q.vertex ⟨p, by omega⟩ = q.vertex ⟨p, by omega⟩ := rfl
  have hpv : q.vertex ⟨p - 1, by omega⟩ = flip (coordOf a) (q.vertex ⟨p, by omega⟩) := by
    apply Fin.ext
    show _ = (q.vertex ⟨p, by omega⟩).val ^^^ 2 ^ (a % 9)
    rw [hprev, hx, Nat.mod_eq_of_lt ha]
  have hnv : q.vertex ⟨p + 1, by omega⟩ = flip (coordOf b) (q.vertex ⟨p, by omega⟩) := by
    apply Fin.ext
    show _ = (q.vertex ⟨p, by omega⟩).val ^^^ 2 ^ (b % 9)
    rw [hnext, hx, Nat.mod_eq_of_lt hb]
  rw [← hx] at e1 e2 e3 e4
  have h := center_counts q ⟨p, by omega⟩ ⟨p - 1, by omega⟩ ⟨p + 1, by omega⟩ (by simp; omega) rfl
    (q.vertex ⟨p, by omega⟩) (coordOf a) (coordOf b) rfl hpv hnv _ e1 e2 (nodupB_nodup e3) e4 _ rfl
  rw [countSeq_eq q p (by omega)]
  rw [hx] at h
  exact h.1

end

/-! ### The main lemma -/

theorem wv_succ (c : List Nat) (i : Nat) : wv c (i + 1) = wv c i ^^^ 2 ^ c.getD i 0 := rfl

theorem wv_pred (c : List Nat) (i : Nat) : wv c i = wv c (i + 1) ^^^ 2 ^ c.getD i 0 := by
  rw [wv_succ, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem winRef_of {D : Sh} {F : CNF} {c roots : List Nat} {rs : List (Nat × Nat)} {C : Clause}
    (hD : shOK D = true) (hok : blocksOK D.T = true) (hT : tabOK D.T [] = true)
    (hc : F.all (check3 D) = true) (hwin : D.T.window = winL c) (h9 : c.all (· < 9) = true)
    (hlex : D.X.map LexT.pairs = (adjP (freeC (c.map coordOf))).map
      (fun g => movedPairs D.T.ball g.1.val g.2.val))
    (hcen : (cenOf c roots).all (cenOK D) = true)
    (hco : ∀ t ∈ cenOf c roots, CornerOK t.2.1 (coordOf t.2.2.1) (coordOf t.2.2.2)
      (cornerVerts t.2.1 t.2.2.1 t.2.2.2))
    (hrs : rs.length + 1 = c.length)
    (hG2 : ∀ τ : Nat → Bool, (∀ x ∈ F, clauseSat τ x) → clauseSat τ C)
    (hcube : C.all (litOff D (specOf roots rs)) = true) : WinRef c rs := by
  intro m q r hr hv hcnt
  have hm : 1 ≤ m := by omega
  obtain ⟨q', hfix, hal, hlexq⟩ := lexmin q (c.map coordOf) D.T.ball (adjP (freeC (c.map coordOf)))
    (gens_free _)
  -- the window is fixed
  have hv' : ∀ i ≤ c.length, vtx q' (r + i) = wv c i := by
    intro i hi
    have e := hv i hi
    rw [vtx_eq q (by omega)] at e
    rw [vtx_eq q' (by omega)]
    rw [hfix ⟨r + i, by omega⟩ (bitsIn_wv c h9 i hi _ e), e]
  have hcs : ∀ k, countSeq q' k = countSeq q k := by
    intro k; unfold countSeq; split
    · exact hal _
    · rfl
  -- G1 hypotheses
  have hwsel : ∀ w ∈ D.T.window, sel q' w = true := by
    intro w hw
    rw [hwin] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hi' := List.mem_range.mp hi
    have e := hv' i (by omega)
    rw [vtx_eq q' (by omega)] at e
    rw [← e]; exact sel_vertex q' _
  have hH : Hyp D.T (sel q') := ⟨hwsel, sel_bad q', sel_deg q' hm,
    blocks_of_tabOK hT (fun s hs => absurd hs List.not_mem_nil) (endSem_count q')⟩
  have hX : ∀ g ∈ D.X, LexOKP (sel q') g.pairs := by
    intro g hg
    have : g.pairs ∈ D.X.map LexT.pairs := List.mem_map_of_mem hg
    rw [hlex] at this
    obtain ⟨g', hg', he⟩ := List.mem_map.mp this
    rw [← he]
    exact lexOK_filter _ _ (hlexq g' hg')
  have hsat : ∀ x ∈ F, clauseSat (tau3 D (sel q')) x :=
    fun x hx => sound3 hD hH hok hX (List.all_eq_true.mp hc x hx)
  -- the counts of the totalizer roots
  have hspec : ∀ t ∈ specOf roots rs, InR t.2.1 t.2.2 (cnt (baseVal D.T (sel q')) (nodeL D.Tot t.1)) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    have hi' := List.mem_range.mp hi
    have hmem : (roots.getD i 0, wv c (i + 1), c.getD i 0, c.getD (i + 1) 0) ∈ cenOf c roots :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
    have hok' := List.all_eq_true.mp hcen _ hmem
    simp only [cenOK, Bool.and_eq_true, beq_iff_eq] at hok'
    have hco' := hco _ hmem
    simp only at hco'
    have ha9 := List.all_eq_true.mp h9 _ (getD_mem c i (by omega))
    have hb9 := List.all_eq_true.mp h9 _ (getD_mem c (i + 1) (by omega))
    simp only [decide_eq_true_eq] at ha9 hb9
    have hcount := centreW q' (r + i + 1) (by omega) (by omega) (wv c (i + 1)) (c.getD i 0)
      (c.getD (i + 1) 0) ha9 hb9 (by rw [show r + i + 1 = r + (i + 1) by omega]; exact hv' _ (by omega))
      (by rw [show r + i + 1 - 1 = r + i by omega, hv' i (by omega), wv_pred c i])
      (by rw [show r + i + 1 + 1 = r + (i + 1 + 1) by omega, hv' _ (by omega), wv_succ]) hco'
    simp only
    rw [cnt_negBall_eq hok'.1, hok'.2, hcount, hcs]
    exact hcnt i hi'
  exact cube_false hspec hcube (hG2 _ hsat)

end S235
