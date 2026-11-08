import Share185Definitions
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
/-! ## Soundness -/



theorem lv_congr {τ₁ τ₂ : Nat → Bool} {a : Nat} (h : τ₁ (a / 2) = τ₂ (a / 2)) :
    lv τ₁ a = lv τ₂ a := by
  unfold lv; rw [h]

theorem lv_negL (τ : Nat → Bool) {x : Nat} (hx : 2 ≤ x) : lv τ (negL x) = !lv τ x := by
  unfold negL lv
  by_cases h : x % 2 = 0
  · have h1 : (x + 1) % 2 = 1 := by omega
    have h2 : (x + 1) / 2 = x / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (x - 1) % 2 = 0 := by omega
    have h2 : (x - 1) / 2 = x / 2 := by omega
    simp [h, h1, h2]

theorem negL_ge {x : Nat} (hx : 2 ≤ x) : 2 ≤ negL x := by
  unfold negL; split <;> omega

theorem oldVar_of_isP {x : Nat} (h : isP M x = true) : oldVar M x = true := by
  simp [oldVar, isP_get h]

theorem oldVar_of_isE {x : Nat} (h : isE M x = true) : oldVar M x = true := by
  simp [oldVar, isE_get h]

theorem tauS_old {x : Nat} (h : oldVar M x = true) :
    tauS S E M X Mr cs tots x = tau S E M cs x := by
  unfold tauS; rw [if_pos h]

theorem baseS_old {x : Nat} (h : oldVar M x = true) :
    baseS S E M X Mr x = base S E M x := by
  unfold baseS; rw [if_pos h]

theorem sqOf_get {a q x y : Nat} (h : sqOf X a = some (q, x, y)) : X.get (a / 2) = .sq q x y := by
  unfold sqOf at h; split at h <;> simp_all

theorem uOf_get {a q t : Nat} (h : uOf X a = some (q, t)) : X.get (a / 2) = .u q t := by
  unfold uOf at h; split at h <;> simp_all

theorem sqOf_of_isSq {a : Nat} (h : isSq X a = true) :
    sqOf X a = some (sqQ X a, sqAB X a) := by
  unfold isSq at h; unfold sqQ sqAB
  cases hs : sqOf X a with
  | none => rw [hs] at h; simp at h
  | some r => simp

theorem uOf_of_isU {a : Nat} (h : isU X a = true) : uOf X a = some (uQT X a) := by
  unfold isU at h; unfold uQT
  cases hs : uOf X a with
  | none => rw [hs] at h; simp at h
  | some r => simp

theorem sval_sq {a : Nat} (h : isSq X a = true) :
    sval S Mr X (a / 2) = emptyPred S (sqQ X a) (sqAB X a) := by
  have := sqOf_get (sqOf_of_isSq h)
  unfold sval; rw [this]; rfl

theorem sval_u {a : Nat} (h : isU X a = true) :
    sval S Mr X (a / 2) = decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  have := uOf_get (uOf_of_isU h)
  unfold sval; rw [this]; rfl

theorem tauS_su {a : Nat} (hn : oldVar M (a / 2) = false) (h : isSq X a = true ∨ isU X a = true) :
    tauS S E M X Mr cs tots (a / 2) = sval S Mr X (a / 2) := by
  unfold tauS; rw [if_neg (by simp [hn])]
  rcases h with h | h
  · rw [sqOf_get (sqOf_of_isSq h)]
  · rw [uOf_get (uOf_of_isU h)]

/-- On a totalizer input, `tauS` and `baseS` agree. -/
theorem lv_base_ok {l : Nat} (h : baseOKS M X l = true) :
    lv (tauS S E M X Mr cs tots) l = lv (baseS S E M X Mr) l := by
  simp only [baseOKS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  apply lv_congr
  by_cases ho : oldVar M (l / 2) = true
  · rw [if_pos ho, Bool.or_eq_true] at h
    rw [tauS_old ho, baseS_old ho]
    rcases h with hp | hp
    · simp [tau, base, isP_get hp]
    · simp [tau, base, isE_get hp]
  · rw [if_neg ho, Bool.or_eq_true] at h
    have hn : oldVar M (l / 2) = false := by simpa using ho
    rw [tauS_su hn h]
    unfold baseS; rw [if_neg ho]

theorem posS_parts {a : Nat} (h : posS M a = true) :
    a % 2 = 0 ∧ 2 ≤ a ∧ oldVar M (a / 2) = false := by
  simp only [posS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lit_posP_S {a : Nat} (h : posP M a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) = S (vl M a) := by
  have h' := h
  simp only [posP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  obtain ⟨⟨h0, h2⟩, hp⟩ := h'
  rw [decode_eq _ h2]
  simp [lv, h0, tauS_old (oldVar_of_isP hp), tau, vl, isP_get hp]

theorem base_posSq {a : Nat} (h : posSq M X a = true) :
    lv (baseS S E M X Mr) a = emptyPred S (sqQ X a) (sqAB X a) := by
  simp only [posSq, Bool.and_eq_true] at h
  obtain ⟨h0, h2, hn⟩ := posS_parts h.1
  simp only [lv, h0, if_true]
  unfold baseS; rw [if_neg (by simp [hn]), sval_sq h.2]

theorem base_posU {a : Nat} (h : posU M X a = true) :
    lv (baseS S E M X Mr) a = decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  simp only [posU, Bool.and_eq_true] at h
  obtain ⟨h0, h2, hn⟩ := posS_parts h.1
  simp only [lv, h0, if_true]
  unfold baseS; rw [if_neg (by simp [hn]), sval_u h.2]

theorem lit_posSq {a : Nat} (h : posSq M X a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) = emptyPred S (sqQ X a) (sqAB X a) := by
  have h' := h
  simp only [posSq, Bool.and_eq_true] at h'
  obtain ⟨h0, h2, hn⟩ := posS_parts h'.1
  rw [decode_eq _ h2]
  simp only [lv, h0, if_true]
  rw [tauS_su hn (Or.inl h'.2), sval_sq h'.2]

theorem lit_posU {a : Nat} (h : posU M X a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) =
      decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  have h' := h
  simp only [posU, Bool.and_eq_true] at h'
  obtain ⟨h0, h2, hn⟩ := posS_parts h'.1
  rw [decode_eq _ h2]
  simp only [lv, h0, if_true]
  rw [tauS_su hn (Or.inr h'.2), sval_u h'.2]

theorem tInfo_sem {i a lo hi c : Nat} (h : tInfo M X i a = some (lo, hi, c)) :
    lv (tauS S E M X Mr cs tots) a = decide (c ≤ bc S E M X Mr tots i lo hi) := by
  unfold tInfo at h
  split at h
  · rename_i hp
    obtain ⟨h0, _, hn⟩ := posS_parts hp
    split at h
    · rename_i i' lo' hi' c' hX
      split at h
      · rename_i hi'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        subst hi'
        simp only [lv, h0, if_true]
        unfold tauS; rw [if_neg (by simp [hn]), hX]
      · simp at h
    · simp at h
  · simp at h


end Snake9.LocalWindow.Tags185
