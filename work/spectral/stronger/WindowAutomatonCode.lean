/-
Cheap kernel versions of the two tests of the table module: shape membership through a code
bitset, and the induced-path test through xor masks of the directions.

The table module of a generated chain must show that every induced restricted growth
string of length `L + 1` is a listed shape followed by a label.  Deciding `c.take L ∈ shapes`
by list equality costs the kernel about 34 x 7 element comparisons per string; testing one bit
of the bitset of shape codes (`maskOf shapeCode shapes`) costs a shift and a mask.  The code
`shapeCode` (base 8, leading sentinel) is injective on lists of digits below 8 of equal length,
which is what `codeFrom_inj` proves.  Core Lean only.
-/
import WindowAutomatonDefs
import WindowAutomatonLoop

namespace Snake9.WindowAutomaton

/-- Bitset of the codes `f s`, `s ∈ l`. -/
def maskOf (f : List Nat → Nat) : List (List Nat) → Nat
  | [] => 0
  | s :: l => maskOf f l ||| 1 <<< f s

theorem testBit_maskOf (f : List Nat → Nat) : ∀ (l : List (List Nat)) (i : Nat),
    Nat.testBit (maskOf f l) i = true → ∃ s, s ∈ l ∧ f s = i
  | [], i, h => by simp [maskOf] at h
  | s :: l, i, h => by
    simp only [maskOf, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨t, ht, hft⟩ := testBit_maskOf f l i h
      exact ⟨t, List.mem_cons_of_mem _ ht, hft⟩
    · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at h
      exact ⟨s, List.mem_cons_self .., by simpa using h⟩

theorem codeFrom_split : ∀ (l : List Nat) (acc : Nat),
    codeFrom l acc = acc * 8 ^ l.length + codeFrom l 0
  | [], acc => by simp [codeFrom]
  | a :: l, acc => by
    simp only [codeFrom, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [codeFrom_split l (acc * 8 + a), codeFrom_split l a, Nat.pow_succ, Nat.add_mul,
      Nat.mul_assoc acc 8 (8 ^ l.length), Nat.mul_comm 8 (8 ^ l.length), Nat.add_assoc]

theorem codeFrom_lt : ∀ (l : List Nat), (∀ a, a ∈ l → a < 8) → codeFrom l 0 < 8 ^ l.length
  | [], _ => by simp [codeFrom]
  | a :: l, h => by
    simp only [codeFrom, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [codeFrom_split l a, Nat.pow_succ]
    have ha : a < 8 := h a (List.mem_cons_self ..)
    have hl := codeFrom_lt l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have h1 : a * 8 ^ l.length + codeFrom l 0 < (a + 1) * 8 ^ l.length := by
      rw [Nat.succ_mul]; exact Nat.add_lt_add_left hl _
    exact Nat.lt_of_lt_of_le h1 (by rw [Nat.mul_comm (8 ^ l.length) 8]; exact Nat.mul_le_mul_right _ ha)

theorem codeFrom_inj : ∀ (l l' : List Nat) (acc : Nat), l.length = l'.length →
    (∀ a, a ∈ l → a < 8) → (∀ a, a ∈ l' → a < 8) → codeFrom l acc = codeFrom l' acc → l = l'
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _, _ => by simp at hl
  | a :: l, a' :: l', acc, hl, h, h', e => by
    simp only [codeFrom] at e
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have e0 := e
    rw [codeFrom_split l, codeFrom_split l', hl] at e
    have hc := codeFrom_lt l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have hc' := codeFrom_lt l' (fun b hb => h' b (List.mem_cons_of_mem _ hb))
    rw [hl] at hc
    have hB : 0 < 8 ^ l'.length := Nat.pow_pos (by decide)
    have e1 : acc * 8 + a = acc * 8 + a' := by
      have := congrArg (· / 8 ^ l'.length) e
      simp only at this
      rw [Nat.add_comm _ (codeFrom l 0), Nat.add_comm _ (codeFrom l' 0), Nat.add_mul_div_right _ _ hB,
        Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hc'] at this
      omega
    have haa : a = a' := by omega
    subst haa
    rw [codeFrom_inj l l' _ hl (fun b hb => h b (List.mem_cons_of_mem _ hb))
      (fun b hb => h' b (List.mem_cons_of_mem _ hb)) e0]

theorem isRGS_bound : ∀ (l : List Nat) (m : Nat), isRGS l m = true → ∀ a, a ∈ l → a < m + l.length
  | [], _, _, a, ha => by simp at ha
  | b :: l, m, h, a, ha => by
    simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.length_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := isRGS_bound l _ h.2 a ha
      split at this <;> omega

theorem isRGS_append : ∀ (l l' : List Nat) (m : Nat), isRGS (l ++ l') m = true → isRGS l m = true
  | [], _, _, _ => rfl
  | b :: l, l', m, h => by
    simp only [List.cons_append, isRGS, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, isRGS_append l l' _ h.2⟩


/-! ### The induced-path test through xor masks

`oddCount seg` (directions used an odd number of times) is the popcount of the xor of the
direction bits; `blockOK` asks for it to be nonzero and, for blocks of two or more steps, not
one.  `fastOK` tests the mask instead: nonzero, and not a power of two.  Only the direction
`blockOK → fastOK` is needed (the kernel loop may reject nothing that is induced). -/

def xorMask : List Nat → Nat
  | [] => 0
  | d :: l => xorMask l ^^^ (1 <<< d)

theorem testBit_xorMask : ∀ (l : List Nat) (d : Nat),
    Nat.testBit (xorMask l) d = (l.count d % 2 == 1)
  | [], d => by simp [xorMask]
  | e :: l, d => by
    simp only [xorMask, Nat.testBit_xor, testBit_xorMask l d, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.testBit_two_pow, List.count_cons]
    by_cases h : e = d
    · subst h
      simp only [decide_true, beq_self_eq_true, if_true]
      rcases Nat.mod_two_eq_zero_or_one (l.count e) with h0 | h0 <;> simp [h0, Nat.add_mod]
    · simp [h]

theorem xorMask_lt : ∀ (l : List Nat), (∀ d, d ∈ l → d < 9) → xorMask l < 2 ^ 9
  | [], _ => by simp [xorMask]
  | e :: l, h => by
    simp only [xorMask]
    apply Nat.xor_lt_two_pow (xorMask_lt l (fun d hd => h d (List.mem_cons_of_mem _ hd)))
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    have hp : ∀ e, e < 9 → 2 ^ e < 2 ^ 9 := by decide
    exact hp e (h e (List.mem_cons_self ..))

/-- `fastOK' X n`: the mask `X` of a block of `n` steps is nonzero and, for `n >= 2`, not a
power of two. -/
def fastOK' (X n : Nat) : Bool := X != 0 && (n < 2 || (X &&& (X - 1)) != 0)

/-- The block test on the xor mask (forced once to a numeral by `letN`). -/
def fastOK (seg : List Nat) : Bool := letN (xorMask seg + 1) fun X => fastOK' X seg.length

theorem fastOK_eq (seg : List Nat) : fastOK seg = fastOK' (xorMask seg) seg.length := letN_succ _ _

def inducedFast (ds : List Nat) : Bool := (blocks ds).all fastOK

theorem two_bits_kernel : allBelowR 512 (fun X => allBelowR 9 (fun a => allBelowR 9 (fun b =>
    (a == b) || !(Nat.testBit X a) || !(Nat.testBit X b) || ((X &&& (X - 1)) != 0)))) = true := by
  decide +kernel

theorem two_bits (X a b : Nat) (hX : X < 512) (ha : a < 9) (hb : b < 9) (hab : a ≠ b)
    (ta : Nat.testBit X a = true) (tb : Nat.testBit X b = true) : (X &&& (X - 1)) ≠ 0 := by
  have h := allBelowR_spec _ _ (allBelowR_spec _ _ (allBelowR_spec _ _ two_bits_kernel X hX) a ha) b hb
  simp only [ta, tb, Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · exact absurd h hab
  · exact h

theorem firsts_nodup : ∀ (seen l : List Nat), seen.Nodup → (firsts seen l).Nodup
  | seen, [], h => by
    simp only [firsts]
    exact List.pairwise_reverse.mpr (h.imp Ne.symm)
  | seen, d :: ds, h => by
    simp only [firsts]
    split
    · exact firsts_nodup _ _ h
    · exact firsts_nodup _ _ (List.nodup_cons.mpr ⟨by assumption, h⟩)

theorem mem_of_mem_firsts : ∀ (seen l : List Nat) (x : Nat), x ∈ firsts seen l → x ∈ seen ∨ x ∈ l
  | seen, [], x, h => by
    simp only [firsts, List.mem_reverse] at h
    exact Or.inl h
  | seen, d :: ds, x, h => by
    simp only [firsts] at h
    rcases mem_of_mem_firsts _ _ x h with h' | h'
    · split at h'
      · exact Or.inl h'
      · rcases List.mem_cons.mp h' with rfl | h''
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h''
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem two_of_nodup : ∀ (l : List Nat), l.Nodup → 2 ≤ l.length → ∃ a b, a ≠ b ∧ a ∈ l ∧ b ∈ l
  | a :: b :: _, h, _ =>
    ⟨a, b, fun e => (List.nodup_cons.mp h).1 (e ▸ List.mem_cons_self ..),
      List.mem_cons_self .., List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

theorem fastOK_of_blockOK (seg : List Nat) (hs : ∀ d, d ∈ seg → d < 9) (h : blockOK seg = true) :
    fastOK seg = true := by
  rw [fastOK_eq]
  unfold blockOK oddCount at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have hodd : ∀ d, d ∈ (firsts [] seg).filter (fun d => seg.count d % 2 == 1) →
      Nat.testBit (xorMask seg) d = true ∧ d < 9 := by
    intro d hd
    rw [List.mem_filter] at hd
    refine ⟨by rw [testBit_xorMask]; exact hd.2, ?_⟩
    rcases mem_of_mem_firsts [] seg d hd.1 with h' | h'
    · simp at h'
    · exact hs d h'
  have hX : xorMask seg ≠ 0 := by
    obtain ⟨d, hd⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero h0)
    intro hz
    have := (hodd d hd).1
    rw [hz, Nat.zero_testBit] at this
    exact Bool.false_ne_true this
  unfold fastOK'
  rw [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, bne_iff_ne, decide_eq_true_eq]
  refine ⟨hX, ?_⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · right
    have hnd : ((firsts [] seg).filter (fun d => seg.count d % 2 == 1)).Nodup :=
      List.Sublist.nodup List.filter_sublist (firsts_nodup [] seg List.nodup_nil)
    obtain ⟨a, b, hab, ha, hb⟩ := two_of_nodup _ hnd (by omega)
    exact two_bits (xorMask seg) a b (xorMask_lt seg hs) (hodd a ha).2 (hodd b hb).2 hab
      (hodd a ha).1 (hodd b hb).1

theorem mem_of_mem_prefixes : ∀ (l b : List Nat), b ∈ prefixes l → ∀ x, x ∈ b → x ∈ l
  | [], b, h, _, _ => by simp [prefixes] at h
  | a :: l, b, h, x, hx => by
    simp only [prefixes, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨b', hb', rfl⟩
    · simp only [List.mem_singleton] at hx
      subst hx; exact List.mem_cons_self ..
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_mem_prefixes l b' hb' x hx')

theorem mem_of_mem_blocks : ∀ (l b : List Nat), b ∈ blocks l → ∀ x, x ∈ b → x ∈ l
  | [], b, h, _, _ => by simp [blocks] at h
  | a :: l, b, h, x, hx => by
    simp only [blocks, List.mem_append] at h
    rcases h with h | h
    · exact mem_of_mem_prefixes _ _ h x hx
    · exact List.mem_cons_of_mem _ (mem_of_mem_blocks l b h x hx)

theorem inducedFast_of_inducedPattern (ds : List Nat) (hd : ∀ d, d ∈ ds → d < 9)
    (h : inducedPattern ds = true) : inducedFast ds = true := by
  unfold inducedPattern at h
  unfold inducedFast
  rw [List.all_eq_true] at h ⊢
  intro b hb
  exact fastOK_of_blockOK b (fun x hx => hd x (mem_of_mem_blocks ds b hb x hx)) (h b hb)

end Snake9.WindowAutomaton
