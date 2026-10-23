import ShareG1
/-!
# Share CNFs: from a snake through the window to a share lower bound

`termOK D c t` relates term `t` of a share CNF with window shape `c` to the share term
`SquareIncidence.shareTerm` of its centre `x = wv c (cen + 1)`, direction `k` and pair `{a, b}`:
its `E` variable names a square containing the four vertices of `Q = x ^ e_k + span(e_a, e_b)`,
and every bit at index `i` is `E` (`i < 2`) or a `g` variable whose corners `pv` are a sublist of the
three other corners of `P = x + span(e_a, e_b)` with a threshold that forces `6/m ≥ i + 1`
(`gBound`).  The terms are listed in strictly increasing order of `(cen, k, a, b)`, so distinct
terms are distinct share terms, and the term values sum to at most the window's share sum
(`rsum_le_windowShare`).

`shareRef_of`: a refuted share CNF (G2: `unsat F`; G1: `check4`, `nodesOK`, `termsOK`) whose bound
is `B` proves `B + 1 ≤ windowShareK q (c.length - 1) r` for every snake `q` through the window.
-/
namespace SH234
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1 S235 Snake9.ShareBonus
open Classical

def corners4 (y a b : Nat) : List Nat := [y, y ^^^ 2 ^ a, y ^^^ 2 ^ b, y ^^^ 2 ^ a ^^^ 2 ^ b]
def p3 (x a b : Nat) : List Nat := [x ^^^ 2 ^ a, x ^^^ 2 ^ b, x ^^^ 2 ^ a ^^^ 2 ^ b]

/-- A true `g` bit with corners `pv` (a sublist of the three) and threshold `t` forces `6/m ≥ gBound`. -/
def gBound (pv : List Nat) (t : Nat) : Nat :=
  if t = 0 ∧ pv.length = 3 then 6 else if t + 2 ≤ pv.length then 3 else 2

def bitOK (D : SD) (x a b e i : Nat) : Lit → Bool
  | .ofNat v => (v == e && decide (i + 1 ≤ 2)) ||
      (match infoOf D v with
       | .g e' pv t => e' == e && pv.isSublist (p3 x a b) && decide (i + 1 ≤ gBound pv t)
       | _ => false)
  | _ => false

def termOK (D : SD) (c : List Nat) (t : Nat) : Bool :=
  let T := termOf D t
  let x := wv c (T.cen + 1)
  decide (T.cen + 1 < c.length) && decide (T.k < 9) && decide (T.a < T.b) && decide (T.b < 9) &&
    T.k != T.a && T.k != T.b &&
    (match infoOf D T.e with
     | .e sq => (corners4 (x ^^^ 2 ^ T.k) T.a T.b).all sq.contains
     | _ => false) &&
    (List.range T.bits.length).all (fun i => bitOK D x T.a T.b T.e i (T.bits.getD i 0))

def code (T : Term) : Nat := ((T.cen * 9 + T.k) * 9 + T.a) * 9 + T.b

def codeLt (D : SD) (t : Nat) : Bool := decide (code (termOf D t) < code (termOf D (t + 1)))

def TermsOK (D : SD) (c : List Nat) : Prop :=
  (∀ t < D.NT, termOK D c t = true) ∧ (∀ t, t + 1 < D.NT → codeLt D t = true)

/-! ### Keys -/

def pairOf (a b : Nat) : AxisPair :=
  if h : (coordOf a).val < (coordOf b).val then ⟨(coordOf a, coordOf b), h⟩ else ⟨(0, 1), by decide⟩

def keyOf (T : Term) : Nat × Coord × AxisPair := (T.cen, coordOf T.k, pairOf T.a T.b)

theorem coordOf_val {a : Nat} (h : a < 9) : (coordOf a).val = a := Nat.mod_eq_of_lt h

theorem pairOf_val {a b : Nat} (hab : a < b) (hb : b < 9) :
    (pairOf a b).val.1.val = a ∧ (pairOf a b).val.2.val = b := by
  unfold pairOf
  rw [dif_pos (by rw [coordOf_val (by omega), coordOf_val hb]; exact hab)]
  exact ⟨coordOf_val (by omega), coordOf_val hb⟩

/-! ### One term -/

section
variable {D : SD} {m : Nat} (q : Snake m)

theorem selected_eq (v : Vertex) : selected q v = if sel q v.val = true then 1 else 0 := by
  unfold selected
  by_cases h : sel q v.val = true
  · rw [if_pos ((inPath_iff_sel q v).mpr h), if_pos h]
  · rw [if_neg (fun hc => h ((inPath_iff_sel q v).mp hc)), if_neg h]

theorem cntS_three (S : Nat → Bool) (u v w : Nat) :
    cntS S [u, v, w] = (if S u = true then 1 else 0) + (if S v = true then 1 else 0) +
      (if S w = true then 1 else 0) := by
  unfold cntS
  simp only [List.filter_cons, List.filter_nil]
  cases S u <;> cases S v <;> cases S w <;> simp

theorem sqCount_eq (X : Vertex) (hX : InPath q X) (a b : Coord) (hab : a.val < b.val) :
    sqCount q ⟨(a, b), hab⟩ X = 1 + cntS (sel q) (p3 X.val a.val b.val) := by
  unfold sqCount p3
  rw [cntS_three]
  simp only [selected_eq]
  rw [if_pos ((inPath_iff_sel q X).mp hX)]
  have e1 : (flip a X).val = X.val ^^^ 2 ^ a.val := rfl
  have e2 : (flip b X).val = X.val ^^^ 2 ^ b.val := rfl
  have e3 : (flip b (flip a X)).val = X.val ^^^ 2 ^ a.val ^^^ 2 ^ b.val := rfl
  simp only [e1, e2, e3]
  omega

theorem sqCount_le (X : Vertex) (a b : Coord) (hab : a.val < b.val) (hX : InPath q X) :
    cntS (sel q) (p3 X.val a.val b.val) ≤ 2 := by
  have h := no_full_square q X ⟨(a, b), hab⟩
  unfold p3; rw [cntS_three]
  simp only at h
  rw [inPath_iff_sel, inPath_iff_sel, inPath_iff_sel, inPath_iff_sel] at h
  have e1 : (flip a X).val = X.val ^^^ 2 ^ a.val := rfl
  have e2 : (flip b X).val = X.val ^^^ 2 ^ b.val := rfl
  have e3 : (flip b (flip a X)).val = X.val ^^^ 2 ^ a.val ^^^ 2 ^ b.val := rfl
  rw [e1, e2, e3, (inPath_iff_sel q X).mp hX] at h
  split <;> split <;> split <;> simp_all

theorem empty_eq_one (X : Vertex) (k a b : Coord) (hab : a.val < b.val) (sq : List Nat)
    (hc : (corners4 (X.val ^^^ 2 ^ k.val) a.val b.val).all sq.contains = true)
    (he : sq.all (fun w => !sel q w) = true) : empty q ⟨(a, b), hab⟩ (flip k X) = 1 := by
  have hn : ∀ w ∈ corners4 (X.val ^^^ 2 ^ k.val) a.val b.val, sel q w = false := by
    intro w hw
    have h1 := List.contains_iff_mem.mp (List.all_eq_true.mp hc w hw)
    simpa using List.all_eq_true.mp he w h1
  unfold empty
  rw [if_pos]
  simp only [inPath_iff_sel]
  have e0 : (flip k X).val = X.val ^^^ 2 ^ k.val := rfl
  have e1 : (flip a (flip k X)).val = X.val ^^^ 2 ^ k.val ^^^ 2 ^ a.val := rfl
  have e2 : (flip b (flip k X)).val = X.val ^^^ 2 ^ k.val ^^^ 2 ^ b.val := rfl
  have e3 : (flip b (flip a (flip k X))).val = X.val ^^^ 2 ^ k.val ^^^ 2 ^ a.val ^^^ 2 ^ b.val := rfl
  simp only [e0, e1, e2, e3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [hn _ (by simp [corners4])]; simp)

theorem shareWeight_ge (n : Nat) (h1 : 1 ≤ n) (h3 : n ≤ 3) : 2 ≤ shareWeight n := by
  unfold shareWeight; split_ifs <;> omega

theorem cnt_p3_le (S : Nat → Bool) {pv l : List Nat} (h : pv.Sublist l) (hl : l.length = 3) :
    cntS S l + pv.length ≤ cntS S pv + 3 := by
  have h1 := cntS_compl S l
  have h2 := cntS_compl S pv
  have h3 := (h.filter (fun w => !S w)).length_le
  omega

/-- A term's value is at most its share term. -/
theorem tval_le (c : List Nat) (t : Nat) (h : termOK D c t = true) (X : Vertex) (hX : InPath q X)
    (hx : X.val = wv c ((termOf D t).cen + 1)) :
    tval D (sel q) t ≤ shareTerm q (keyOf (termOf D t)).2.1 (keyOf (termOf D t)).2.2 X := by
  generalize hT : termOf D t = T at h hx ⊢
  unfold termOK at h
  rw [hT] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hk⟩, hab⟩, hb⟩, hka⟩, hkb⟩, hE⟩, hbits⟩ := h
  rw [← hx] at hE hbits
  split at hE
  · rename_i sq hsq
    obtain ⟨pa, pb⟩ := pairOf_val hab hb
    have hk' := coordOf_val hk
    unfold keyOf
    simp only
    generalize hP : pairOf T.a T.b = P at pa pb
    obtain ⟨⟨a', b'⟩, hab'⟩ := P
    simp only at pa pb
    rw [← pa] at hE hbits hka
    rw [← pb] at hE hbits hkb
    unfold shareTerm
    rw [if_pos (by
      unfold offAxis; simp only
      exact ⟨fun h => hka (by rw [← hk']; exact congrArg Fin.val h),
        fun h => hkb (by rw [← hk']; exact congrArg Fin.val h)⟩)]
    rw [sqCount_eq q X hX a' b' hab']
    have hle := sqCount_le q X a' b' hab' hX
    -- E true gives the empty square
    have hEtrue : ∀ i, i < T.bits.length → litSat (tau1 D (sel q)) (T.bits.getD i 0) = true →
        empty q ⟨(a', b'), hab'⟩ (flip (coordOf T.k) X) = 1 ∧
        i + 1 ≤ shareWeight (1 + cntS (sel q) (p3 X.val a'.val b'.val)) := by
      intro i hi hs
      have hbo := hbits i hi
      generalize T.bits.getD i 0 = l at hbo hs
      match l, hbo with
      | .ofNat v, hbo =>
        simp only [bitOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbo
        have hs' : tau1 D (sel q) v = true := hs
        rcases hbo with ⟨rfl, hi2⟩ | hg
        · have hvs : ¬ T.e < D.VS := by intro hc; rw [infoOf_lt hc] at hsq; exact absurd hsq (by simp)
          unfold tau1 egVal at hs'
          rw [if_neg hvs, hsq] at hs'
          refine ⟨empty_eq_one q X _ a' b' hab' sq (by rw [hk']; exact hE) hs', ?_⟩
          have := shareWeight_ge (1 + cntS (sel q) (p3 X.val a'.val b'.val)) (by omega) (by omega)
          omega
        · split at hg
          · rename_i e' pv t' hgv
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isSublist_iff_sublist] at hg
            obtain ⟨⟨rfl, hsub⟩, hib⟩ := hg
            have hvs : ¬ v < D.VS := by intro hc; rw [infoOf_lt hc] at hgv; exact absurd hgv (by simp)
            unfold tau1 egVal at hs'
            rw [if_neg hvs, hgv] at hs'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hs'
            obtain ⟨hev, hct⟩ := hs'
            rw [eVal_of hsq] at hev
            refine ⟨empty_eq_one q X _ a' b' hab' sq (by rw [hk']; exact hE) hev, ?_⟩
            have h3 := cnt_p3_le (sel q) hsub (by simp [p3])
            unfold gBound at hib
            unfold shareWeight
            split_ifs at hib <;> split_ifs <;> omega
          · exact absurd hg (by simp)
      | .negSucc _, hbo => simp [bitOK] at hbo
    unfold tval
    rw [hT]
    apply topv_le
    intro i hi hs
    obtain ⟨h1, h2⟩ := hEtrue i hi hs
    rw [h1, Nat.one_mul]; omega
  · exact absurd hE (by simp)

end

/-! ### All terms -/

theorem code_mono {D : SD} {c : List Nat} (h : TermsOK D c) :
    ∀ t u, t < u → u < D.NT → code (termOf D t) < code (termOf D u) := by
  have h2 : ∀ t, t < D.NT - 1 → codeLt D t = true := fun t ht => h.2 t (by omega)
  intro t u htu hu
  induction u with
  | zero => omega
  | succ u ih =>
    have := h2 u (by omega)
    simp only [codeLt, decide_eq_true_eq] at this
    rcases Nat.lt_succ_iff_lt_or_eq.mp htu with h' | rfl
    · exact Nat.lt_trans (ih h' (by omega)) this
    · exact this

theorem key_inj {D : SD} {c : List Nat} (h : TermsOK D c) {t u : Nat} (ht : t < D.NT) (hu : u < D.NT)
    (he : keyOf (termOf D t) = keyOf (termOf D u)) : t = u := by
  have hok : ∀ s < D.NT, (termOf D s).k < 9 ∧ (termOf D s).a < (termOf D s).b ∧ (termOf D s).b < 9 := by
    intro s hs
    have := h.1 s hs
    simp only [termOK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1.1.1.1.1.2, this.1.1.1.1.1.2, this.1.1.1.1.2⟩
  obtain ⟨k1, a1, b1⟩ := hok t ht
  obtain ⟨k2, a2, b2⟩ := hok u hu
  have hc : code (termOf D t) = code (termOf D u) := by
    unfold keyOf at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨e1, e2, e3⟩ := he
    have ek := congrArg Fin.val e2
    rw [coordOf_val k1, coordOf_val k2] at ek
    have p1 := pairOf_val a1 b1
    have p2 := pairOf_val a2 b2
    rw [e3] at p1
    unfold code; rw [e1, ek, ← p1.1, ← p1.2, p2.1, p2.2]
  rcases Nat.lt_trichotomy t u with hl | hl | hl
  · have := code_mono h t u hl hu; omega
  · exact hl
  · have := code_mono h u t hl ht; omega

theorem rsum_le_windowShare {D : SD} {c : List Nat} (h : TermsOK D c) {m : Nat} (q : Snake m)
    (r : Nat) (hr : r + c.length ≤ m) (hv : ∀ i ≤ c.length, vtx q (r + i) = wv c i) :
    rsum D (sel q) 0 D.NT ≤ windowShareK q (c.length - 1) r := by
  have hall := h.1
  let G : Nat × Coord × AxisPair → Nat := fun y =>
    if hy : r + 1 + y.1 ≤ m then shareTerm q y.2.1 y.2.2 (q.vertex ⟨r + 1 + y.1, by omega⟩) else 0
  have hcen : ∀ t < D.NT, (termOf D t).cen + 1 < c.length := by
    intro t ht
    have := hall t ht
    simp only [termOK, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1
  have h1 : rsum D (sel q) 0 D.NT ≤ ∑ t ∈ Finset.Ico 0 D.NT, G (keyOf (termOf D t)) := by
    unfold rsum
    apply Finset.sum_le_sum
    intro t ht
    have ht' := (Finset.mem_Ico.mp ht).2
    have hc := hcen t ht'
    have hle : r + 1 + (termOf D t).cen ≤ m := by omega
    simp only [G, keyOf, dif_pos hle]
    apply tval_le q c t (hall t ht') _ ⟨_, rfl⟩
    have := hv ((termOf D t).cen + 1) (by omega)
    rw [vtx_eq q (by omega)] at this
    rw [← this]
    exact congrArg (fun z : Fin (m + 1) => (q.vertex z).val) (Fin.ext (by simp only; omega))
  have h2 : ∑ t ∈ Finset.Ico 0 D.NT, G (keyOf (termOf D t)) =
      ∑ y ∈ (Finset.Ico 0 D.NT).image (fun t => keyOf (termOf D t)), G y := by
    rw [Finset.sum_image]
    intro t ht u hu he
    exact key_inj h (Finset.mem_Ico.mp ht).2 (Finset.mem_Ico.mp hu).2 he
  have h3 : ∑ y ∈ (Finset.Ico 0 D.NT).image (fun t => keyOf (termOf D t)), G y ≤
      ∑ y ∈ (Finset.range (c.length - 1)) ×ˢ (Finset.univ ×ˢ Finset.univ), G y := by
    apply Finset.sum_le_sum_of_subset
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have := hcen t (Finset.mem_Ico.mp ht).2
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, keyOf]
    omega
  have h4 : ∑ y ∈ (Finset.range (c.length - 1)) ×ˢ (Finset.univ ×ˢ Finset.univ), G y =
      windowShareK q (c.length - 1) r := by
    rw [Finset.sum_product]
    unfold windowShareK
    apply Finset.sum_congr rfl
    intro ci hci
    have hci' := Finset.mem_range.mp hci
    have hle : r + 1 + ci ≤ m := by omega
    rw [Finset.sum_product]
    unfold shareSeq
    rw [dif_pos (by omega)]
    unfold share vertexShare
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro ab _
    simp only [G, dif_pos hle]
  omega

/-! ### The window theorem -/

/-- Every snake through the window `wv c` has share sum at least `LB` over the window's centres. -/
def ShareRef (c : List Nat) (LB : Nat) : Prop :=
  ∀ {m : Nat} (q : Snake m) (r : Nat), r + c.length ≤ m → (∀ i ≤ c.length, vtx q (r + i) = wv c i) →
    LB ≤ windowShareK q (c.length - 1) r

theorem shareRef_of {D : SD} {F : CNF} {c : List Nat} (hF : unsat F) (hD : sdOK D = true)
    (hN : NodesOK D) (hok : blocksOK D.T = true) (hT : tabOK D.T [] = true)
    (hc : F.all (check4 D) = true) (hterms : TermsOK D c) (hwin : D.T.window = winL c)
    (hcl : 1 ≤ c.length) : ShareRef c (D.B + 1) := by
  intro m q r hr hv
  by_contra hlt
  have hm : 1 ≤ m := by omega
  have hwsel : ∀ w ∈ D.T.window, sel q w = true := by
    intro w hw
    rw [hwin] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hi' := List.mem_range.mp hi
    have e := hv i (by omega)
    rw [vtx_eq q (by omega)] at e
    rw [← e]; exact sel_vertex q _
  have hH : Hyp D.T (sel q) := ⟨hwsel, sel_bad q, sel_deg q hm,
    blocks_of_tabOK hT (fun s hs => absurd hs List.not_mem_nil) (endSem_count q)⟩
  have hB : rsum D (sel q) 0 D.NT ≤ D.B := by
    have := rsum_le_windowShare hterms q r hr hv; omega
  exact hF (tauS D (sel q)) (fun x hx => sound4 hD hN hH hok hB (List.all_eq_true.mp hc x hx))

end SH234
