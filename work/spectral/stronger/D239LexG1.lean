import D239Lex
/-!
# G1 for symmetry-broken window CNFs

A symmetry-broken CNF is a window CNF (checked by `W223G1.check`, all variables below `VB`) plus
lex-leader clauses for generators `g` (pairs `(v, σ v)` of moved ball vertices, auxiliary variables
`e_1, ..., e_{L-1}` numbered from `g.base ≥ VB`):

    [¬x₀, y₀]                      [¬e_i, ¬x_i, y_i]            (x_i ≤ y_i while equal so far)
    [¬x₀, ¬y₀, e₁], [x₀, y₀, e₁]   [¬e_i, ¬x_i, ¬y_i, e_{i+1}], [¬e_i, x_i, y_i, e_{i+1}]

`tau2` extends the intended assignment `W223G1.tau` by `e_i := eqPre S pairs i`; `check2` accepts
the old clause shapes over variables below `VB` and the lex shapes (`ruleLex`); `sound2` proves
every accepted clause true under `tau2` when the selection satisfies `LexOKP` for every generator.
`RefutedL` packages a refuted symmetry-broken window; `refL_false` applies it to a snake through the
window, after `lexmin` has moved the snake to its lex-least image.
-/
namespace D239
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1

structure LexT where
  pairs : List (Nat × Nat)
  base : Nat

instance : Inhabited LexT := ⟨⟨[], 0⟩⟩

/-- Auxiliary variable `v` is `e_i` (`1 ≤ i < length`) of generator `n` (counting from `n0`). -/
def lexDec (v : Nat) : Nat → List LexT → Option (Nat × Nat)
  | _, [] => none
  | n, g :: gs => if g.base ≤ v ∧ v + 1 < g.base + g.pairs.length then some (n, v + 1 - g.base)
      else lexDec v (n + 1) gs

def gP (X : List LexT) (n : Nat) : List (Nat × Nat) := (X.getD n default).pairs
def pairAt (X : List LexT) (n i : Nat) : Nat × Nat := (gP X n).getD i (0, 0)

def tau2 (T : Tables) (X : List LexT) (VB : Nat) (S : Nat → Bool) (v : Nat) : Bool :=
  if v < VB then tau T S v else
    match lexDec v 0 X with
    | some (n, i) => eqPre S (gP X n) i
    | none => false

def isB (T : Tables) (VB v : Nat) : Bool := isBall T v && decide (v < VB)

/-- `[¬e, ¬x, y]` (step) or `[¬x, ¬y, e₁]`. -/
def ruleNNP (T : Tables) (X : List LexT) (VB a b c : Nat) : Bool :=
  (isB T VB b && isB T VB c && decide (VB ≤ a) &&
    match lexDec a 0 X with
    | some (n, i) => pairAt X n i == (bv T b, bv T c)
    | none => false) ||
  (isB T VB a && isB T VB b && decide (VB ≤ c) &&
    match lexDec c 0 X with
    | some (n, i) => i == 1 && pairAt X n 0 == (bv T a, bv T b)
    | none => false)

def ruleLex (T : Tables) (X : List LexT) (VB : Nat) : Clause → Bool
  | [.negSucc x, .ofNat y] => isB T VB (x + 1) && isB T VB y &&
      X.any (fun g => g.pairs.head? == some (bv T (x + 1), bv T y))
  | [.negSucc a, .negSucc b, .ofNat c] => ruleNNP T X VB (a + 1) (b + 1) c
  | [.ofNat x, .ofNat y, .ofNat e] => isB T VB x && isB T VB y && decide (VB ≤ e) &&
      match lexDec e 0 X with
      | some (n, i) => i == 1 && pairAt X n 0 == (bv T x, bv T y)
      | none => false
  | [.negSucc e, .negSucc x, .negSucc y, .ofNat e'] =>
      isB T VB (x + 1) && isB T VB (y + 1) && decide (VB ≤ e + 1) && decide (VB ≤ e') &&
      match lexDec (e + 1) 0 X, lexDec e' 0 X with
      | some (n, i), some (n', i') => n == n' && i' == i + 1 && pairAt X n i == (bv T (x + 1), bv T (y + 1))
      | _, _ => false
  | [.negSucc e, .ofNat x, .ofNat y, .ofNat e'] =>
      isB T VB x && isB T VB y && decide (VB ≤ e + 1) && decide (VB ≤ e') &&
      match lexDec (e + 1) 0 X, lexDec e' 0 X with
      | some (n, i), some (n', i') => n == n' && i' == i + 1 && pairAt X n i == (bv T x, bv T y)
      | _, _ => false
  | _ => false

def check2 (T : Tables) (X : List LexT) (VB : Nat) (c : Clause) : Bool :=
  (c.all (fun l => decide (l.natAbs < VB)) && check T c) || ruleLex T X VB c

/-! ### Soundness -/

section
variable {T : Tables} {X : List LexT} {VB : Nat} {S : Nat → Bool}

theorem lexDec_spec (v : Nat) : ∀ (X : List LexT) (n0 : Nat) {n i : Nat},
    lexDec v n0 X = some (n, i) → n0 ≤ n ∧ v + 1 = (X.getD (n - n0) default).base + i ∧ 1 ≤ i ∧
      i < (X.getD (n - n0) default).pairs.length
  | [], _, _, _, h => by simp [lexDec] at h
  | g :: gs, n0, n, i, h => by
    unfold lexDec at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Nat.sub_self, List.getD_cons_zero]
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := lexDec_spec v gs (n0 + 1) h
      have e : n - n0 = (n - (n0 + 1)) + 1 := by omega
      rw [e, List.getD_cons_succ]
      exact ⟨by omega, h2, h3, h4⟩

theorem lexDec_inj {v w n i : Nat} (hv : lexDec v 0 X = some (n, i)) (hw : lexDec w 0 X = some (n, i)) :
    v = w := by
  have := lexDec_spec v X 0 hv
  have := lexDec_spec w X 0 hw
  omega

theorem gP_lex (hX : ∀ g ∈ X, LexOKP S g.pairs) (n : Nat) : LexOKP S (gP X n) := by
  unfold gP
  by_cases hn : n < X.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact hX _ (List.getElem_mem hn)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    trivial

theorem tau2_lt {v : Nat} (hv : v < VB) : tau2 T X VB S v = tau T S v := by
  unfold tau2; rw [if_pos hv]

theorem tau2_aux {v n i : Nat} (hv : VB ≤ v) (hd : lexDec v 0 X = some (n, i)) :
    tau2 T X VB S v = eqPre S (gP X n) i := by
  unfold tau2; rw [if_neg (by omega), hd]

theorem tau2_ball {v : Nat} (h : isB T VB v = true) : tau2 T X VB S v = S (bv T v) := by
  simp only [isB, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [tau2_lt h.2, tau_ball h.1]

theorem clauseSat_congr {τ₁ τ₂ : Nat → Bool} {c : Clause} (h : ∀ l ∈ c, τ₁ l.natAbs = τ₂ l.natAbs)
    (hc : clauseSat τ₁ c) : clauseSat τ₂ c := by
  obtain ⟨l, hl, hs⟩ := (clauseSat_iff τ₁ c).mp hc
  refine (clauseSat_iff τ₂ c).mpr ⟨l, hl, ?_⟩
  have := h l hl
  match l with
  | .ofNat n => simp only [litSat] at hs ⊢; rw [← show τ₁ n = τ₂ n from this]; exact hs
  | .negSucc n => simp only [litSat] at hs ⊢; rw [← show τ₁ (n + 1) = τ₂ (n + 1) from this]; exact hs

theorem eqPre_one (P : List (Nat × Nat)) (h : 1 < P.length) :
    eqPre S P 1 = (S (P.getD 0 (0, 0)).1 == S (P.getD 0 (0, 0)).2) := by
  rw [eqPre_succ S P 0 (by omega)]; simp [eqPre]

theorem ruleNNP_sound (hX : ∀ g ∈ X, LexOKP S g.pairs) {a b c : Nat}
    (h : ruleNNP T X VB a b c = true) :
    (!tau2 T X VB S a || !tau2 T X VB S b || tau2 T X VB S c) = true := by
  unfold ruleNNP at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hb, hc⟩, ha⟩, hm⟩ | ⟨⟨⟨ha, hb⟩, hc⟩, hm⟩
  · split at hm
    · rename_i n i hd
      have hp := beq_iff_eq.mp hm
      have hs := lexDec_spec a X 0 hd
      rw [tau2_aux ha hd, tau2_ball hb, tau2_ball hc]
      cases he : eqPre S (gP X n) i
      · rfl
      · cases hx : S (bv T b)
        · rfl
        · have := lexAt S (gP X n) i (gP_lex hX n) (by simpa [gP] using hs.2.2.2) he
          unfold pairAt at hp
          rw [hp] at this
          simp [this hx]
    · exact absurd hm (by simp)
  · split at hm
    · rename_i n i hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, hp⟩ := hm
      have hs := lexDec_spec c X 0 hd
      rw [tau2_aux hc hd, tau2_ball ha, tau2_ball hb, eqPre_one _ (by simpa [gP] using hs.2.2.2)]
      unfold pairAt at hp
      rw [hp]
      cases S (bv T a) <;> cases S (bv T b) <;> rfl
    · exact absurd hm (by simp)

theorem ruleLex_sound (hX : ∀ g ∈ X, LexOKP S g.pairs) {c : Clause} (h : ruleLex T X VB c = true) :
    clauseSat (tau2 T X VB S) c := by
  unfold clauseSat
  match c, h with
  | [.negSucc x, .ofNat y], h =>
    simp only [ruleLex, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hx, hy⟩, g, hg, hh⟩ := h
    simp only [List.any_cons, List.any_nil, Bool.or_false, litSat]
    rw [tau2_ball hx, tau2_ball hy]
    have hl := hX g hg
    match hgp : g.pairs, hh with
    | p :: P, hh =>
      simp only [hgp, List.head?_cons, Option.some.injEq] at hh
      rw [hgp] at hl
      have := hl.1
      rw [hh] at this
      cases hs : S (bv T (x + 1))
      · rfl
      · simp [this hs]
  | [.negSucc a, .negSucc b, .ofNat c], h =>
    simp only [ruleLex] at h
    have := ruleNNP_sound hX h
    simpa [litSat, Bool.or_assoc] using this
  | [.ofNat x, .ofNat y, .ofNat e], h =>
    simp only [ruleLex, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hx, hy⟩, he⟩, hm⟩ := h
    split at hm
    · rename_i n i hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, hp⟩ := hm
      have hs := lexDec_spec e X 0 hd
      simp only [List.any_cons, List.any_nil, Bool.or_false, litSat]
      rw [tau2_aux he hd, tau2_ball hx, tau2_ball hy, eqPre_one _ (by simpa [gP] using hs.2.2.2)]
      unfold pairAt at hp
      rw [hp]
      cases S (bv T x) <;> cases S (bv T y) <;> rfl
    · exact absurd hm (by simp)
  | [.negSucc e, .negSucc x, .negSucc y, .ofNat e'], h =>
    simp only [ruleLex, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hx, hy⟩, he⟩, he'⟩, hm⟩ := h
    split at hm
    · rename_i n i n' i' hd hd'
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨rfl, rfl⟩, hp⟩ := hm
      have hs := lexDec_spec e' X 0 hd'
      simp only [List.any_cons, List.any_nil, Bool.or_false, litSat]
      rw [tau2_aux he hd, tau2_aux he' hd', tau2_ball hx, tau2_ball hy,
        eqPre_succ S _ i (by simp [gP] at hs ⊢; omega)]
      unfold pairAt at hp
      rw [hp]
      cases eqPre S (gP X n) i <;> cases S (bv T (x + 1)) <;> cases S (bv T (y + 1)) <;> rfl
    · exact absurd hm (by simp)
  | [.negSucc e, .ofNat x, .ofNat y, .ofNat e'], h =>
    simp only [ruleLex, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hx, hy⟩, he⟩, he'⟩, hm⟩ := h
    split at hm
    · rename_i n i n' i' hd hd'
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨rfl, rfl⟩, hp⟩ := hm
      have hs := lexDec_spec e' X 0 hd'
      simp only [List.any_cons, List.any_nil, Bool.or_false, litSat]
      rw [tau2_aux he hd, tau2_aux he' hd', tau2_ball hx, tau2_ball hy,
        eqPre_succ S _ i (by simp [gP] at hs ⊢; omega)]
      unfold pairAt at hp
      rw [hp]
      cases eqPre S (gP X n) i <;> cases S (bv T x) <;> cases S (bv T y) <;> rfl
    · exact absurd hm (by simp)

theorem sound2 (hS : Hyp T S) (hok : blocksOK T = true) (hX : ∀ g ∈ X, LexOKP S g.pairs)
    {c : Clause} (h : check2 T X VB c = true) : clauseSat (tau2 T X VB S) c := by
  unfold check2 at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hv, hc⟩ | h
  · exact clauseSat_congr (fun l hl => (tau2_lt (hv l hl)).symm) (sound hS hok hc)
  · exact ruleLex_sound hX h

theorem no_hyp2 {F : CNF} (hF : unsat F) (hok : blocksOK T = true)
    (hc : F.all (check2 T X VB) = true) (hS : Hyp T S) (hX : ∀ g ∈ X, LexOKP S g.pairs) : False :=
  hF (tau2 T X VB S) (fun c hcF => sound2 hS hok hX ((List.all_eq_true.mp hc) c hcF))

end

/-! ### Packaged symmetry-broken refutations -/

def movedPairs (ball : List Nat) (a b : Nat) : List (Nat × Nat) :=
  (ball.map (fun v => (v, swapN a b v))).filter (fun p => p.1 != p.2)

def freeC (W : List Coord) : List Coord := (List.finRange 9).filter (fun c => !W.contains c)

def adjP : List Coord → List (Coord × Coord)
  | a :: b :: l => (a, b) :: adjP (b :: l)
  | _ => []

theorem adjP_mem : ∀ (l : List Coord) (g : Coord × Coord), g ∈ adjP l → g.1 ∈ l ∧ g.2 ∈ l
  | a :: b :: l, g, h => by
    simp only [adjP, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := adjP_mem (b :: l) g h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩
  | [], _, h => by simp [adjP] at h
  | [_], _, h => by simp [adjP] at h

theorem gens_free (W : List Coord) : ∀ g ∈ adjP (freeC W), g.1 ∉ W ∧ g.2 ∉ W := by
  intro g hg
  have := adjP_mem _ g hg
  simp only [freeC, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at this
  exact ⟨this.1.2, this.2.2⟩

/-- A checked, refuted symmetry-broken window CNF: window `win`, centre specifications `sp`,
lex generators the adjacent transpositions of the coordinates outside `W`. -/
def RefutedL (win : List Nat) (sp : List Spec) (W : List Coord) : Prop :=
  ∃ (T : Tables) (F : CNF) (X : List LexT) (VB : Nat), unsat F ∧ blocksOK T = true ∧
    F.all (check2 T X VB) = true ∧ tabOK T sp = true ∧ T.window = win ∧
    X.map LexT.pairs = (adjP (freeC W)).map (fun g => movedPairs T.ball g.1.val g.2.val)

theorem refL_false {m : Nat} (q : Snake m) (hm : 1 ≤ m) {win : List Nat} {sp : List Spec}
    {W : List Coord} (hR : RefutedL win sp W)
    (hfacts : ∀ q' : Snake m, (∀ i, BitsIn W (q.vertex i) → q'.vertex i = q.vertex i) →
      (∀ k, localAlpha q' k = localAlpha q k) →
      (∀ w ∈ win, sel q' w = true) ∧ ∀ s ∈ sp, SpecHolds (sel q') s) : False := by
  obtain ⟨T, F, X, VB, hF, hok, hc, hT, hw, hX⟩ := hR
  obtain ⟨q', hfix, hal, hlex⟩ := lexmin q W T.ball (adjP (freeC W)) (gens_free W)
  obtain ⟨hwin, hsp⟩ := hfacts q' hfix hal
  refine no_hyp2 hF hok hc ⟨hw ▸ hwin, sel_bad q', sel_deg q' hm,
    blocks_of_tabOK hT hsp (endSem_count q')⟩ ?_
  intro g hg
  have : g.pairs ∈ X.map LexT.pairs := List.mem_map_of_mem hg
  rw [hX] at this
  obtain ⟨g', hg', he⟩ := List.mem_map.mp this
  rw [← he]
  exact lexOK_filter _ _ (hlex g' hg')

end D239
