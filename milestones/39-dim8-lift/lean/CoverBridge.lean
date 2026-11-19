import CoverCnf
/-! Bridge for the cover CNFs. -/
set_option linter.deprecated false
set_option maxRecDepth 100000
namespace Dim8Lift.Cover
open Dim8Lift Dim8Lift.Cnf Dim8Lift.Cube Snake9.LocalWindow

theorem fxN_F : ∀ u : Fin 64, ∀ i : Fin 6, (u.val < 32 → i.val < 5 → fx u.val i.val < 32) ∧ fx u.val i.val < 64 := by
  decide
theorem fxN {n u i : Nat} (hn : n = 5 ∨ n = 6) (hu : u < 2 ^ n) (hi : i < n) : fx u i < 2 ^ n := by
  rcases hn with rfl | rfl
  · exact (fxN_F ⟨u, by simp at hu; omega⟩ ⟨i, by omega⟩).1 (by simpa using hu) hi
  · exact (fxN_F ⟨u, by simp at hu; omega⟩ ⟨i, by omega⟩).2

variable (T : Nat → Bool) (ℓ : Nat → Nat)

def tc0 (v : Nat) : Bool :=
  if v = 0 then false
  else if v ≤ 64 then T (v - 1)
  else if v ≤ 4160 then decide ((v - 65) % 64 + 1 ≤ ℓ ((v - 65) / 64))
  else if v ≤ 28736 then
    T (fx ((v - 4161) / 384) ((v - 4161) % 384 / 64)) &&
      !decide ((v - 4161) % 64 + 1 ≤ ℓ (fx ((v - 4161) / 384) ((v - 4161) % 384 / 64)))
  else false

def ctrVal : Nat → List (List Int × Nat) → Nat → Bool
  | _, [], _ => false
  | b, (xs, k) :: rest, v =>
    if v < b + 64 * k then decide ((v - b) % k + 1 ≤ cl (tc0 T ℓ) xs ((v - b) / k + 1))
    else ctrVal (b + 64 * k) rest v

def tc (ctrs : List (List Int × Nat)) (v : Nat) : Bool :=
  if v < cbase then tc0 T ℓ v else ctrVal T ℓ cbase ctrs v

variable {T ℓ}

theorem c_s {u : Nat} (hu : u < 64) : tc0 T ℓ (cs u) = T u := by
  unfold tc0 cs; rw [if_neg (by omega), if_pos (by omega)]; rfl
theorem c_o {u j : Nat} (hu : u < 64) (hj1 : 1 ≤ j) (hj : j ≤ 64) : tc0 T ℓ (co u j) = decide (j ≤ ℓ u) := by
  unfold tc0 co; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show (65 + 64 * u + (j - 1) - 65) % 64 = j - 1 by omega, show (65 + 64 * u + (j - 1) - 65) / 64 = u by omega,
    show j - 1 + 1 = j by omega]
theorem c_a {u i j : Nat} (hu : u < 64) (hi : i < 6) (hj1 : 1 ≤ j) (hj : j ≤ 64) :
    tc0 T ℓ (ca u i j) = (T (fx u i) && !decide (j ≤ ℓ (fx u i))) := by
  unfold tc0 ca; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show (4161 + 384 * u + 64 * i + (j - 1) - 4161) / 384 = u by omega,
    show (4161 + 384 * u + 64 * i + (j - 1) - 4161) % 384 / 64 = i by omega,
    show (4161 + 384 * u + 64 * i + (j - 1) - 4161) % 64 = j - 1 by omega, show j - 1 + 1 = j by omega]

theorem lpp {τ : Nat → Bool} {v : Nat} (h : 0 < v) : litTrue τ (pos v) = τ v := litTrue_pos τ h
theorem lnn {τ : Nat → Bool} {v : Nat} (h : 0 < v) : litTrue τ (neg v) = !τ v := litTrue_neg τ h

theorem tc_lo {ctrs : List (List Int × Nat)} {v : Nat} (h : v < cbase) : tc T ℓ ctrs v = tc0 T ℓ v := by
  unfold tc; rw [if_pos h]

structure Hyp (n : Nat) (T : Nat → Bool) (ℓ : Nat → Nat) : Prop where
  n56 : n = 5 ∨ n = 6
  le : ∀ u, u < 2 ^ n → ℓ u ≤ 64
  deg : ∀ u, u < 2 ^ n → ∀ a b c, a < b → b < c → c < n →
    T u = true → T (fx u a) = true → T (fx u b) = true → T (fx u c) = false
  lvl : ∀ u, u < 2 ^ n → ∀ i1 i2, i1 < i2 → i2 < n → T u = true → T (fx u i1) = true → T (fx u i2) = true →
    ∃ i, i < n ∧ T (fx u i) = true ∧ ℓ (fx u i) < ℓ u

theorem pow_le64 {n : Nat} (hn : n = 5 ∨ n = 6) : 2 ^ n ≤ 64 := by rcases hn with rfl | rfl <;> decide

theorem deg_ok {n : Nat} (h : Hyp n T ℓ) (ctrs : List (List Int × Nat)) :
    ∀ c ∈ cDeg n, clauseTrue (tc T ℓ ctrs) c = true := by
  intro c hc
  simp only [cDeg, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨u, hu, ⟨a, b, d⟩, ht, rfl⟩ := hc
  simp only [triplesN, List.mem_filter, decide_eq_true_eq] at ht
  have ht' := mem_triples8.mp ht.1
  have h64 := pow_le64 h.n56
  have f1 := fxN h.n56 hu (show a < n by omega); have f2 := fxN h.n56 hu (show b < n by omega)
  have f3 := fxN h.n56 hu ht.2
  have hd := h.deg u hu a b d ht'.1 ht'.2.1 ht.2
  simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
  rw [lnn (by unfold cs; omega), lnn (by unfold cs; omega), lnn (by unfold cs; omega), lnn (by unfold cs; omega),
    tc_lo (by unfold cs cbase; omega), tc_lo (by unfold cs cbase; omega), tc_lo (by unfold cs cbase; omega),
    tc_lo (by unfold cs cbase; omega), c_s (by omega), c_s (by omega), c_s (by omega), c_s (by omega)]
  cases h0 : T u <;> cases h1 : T (fx u a) <;> cases h2 : T (fx u b) <;> simp_all

theorem lvl_ok {n : Nat} (h : Hyp n T ℓ) (ctrs : List (List Int × Nat)) :
    ∀ c ∈ cLvl n, clauseTrue (tc T ℓ ctrs) c = true := by
  intro c hc
  simp only [cLvl, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨u, hu, hc⟩ := hc
  have h64 := pow_le64 h.n56
  have hn6 : n ≤ 6 := by rcases h.n56 with rfl | rfl <;> omega
  have lo : ∀ v, v ≤ 28736 → tc T ℓ ctrs v = tc0 T ℓ v := fun v hv => tc_lo (by unfold cbase; omega)
  have vs : ∀ x, 0 < cs x := by intro x; unfold cs; omega
  have vo : ∀ x j, 0 < co x j := by intro x j; unfold co; omega
  have va : ∀ x i j, 0 < ca x i j := by intro x i j; unfold ca; omega
  unfold cLvlU at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j0, hj0, rfl⟩ := hc
      simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [lnn (vo _ _), lpp (vo _ _), lo _ (by unfold co; omega), lo _ (by unfold co; omega),
        c_o (by omega) (by omega) (by omega), c_o (by omega) (by omega) (by omega)]
      simp; omega
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain ⟨i, hi, j0, hj0, hc⟩ := hc
      have hf := fxN h.n56 hu hi
      rcases hc with rfl | rfl
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [lnn (va _ _ _), lpp (vs _), lo _ (by unfold ca; omega), lo _ (by unfold cs; omega),
          c_a (by omega) (by omega) (by omega) (by omega), c_s (by omega)]
        cases T (fx u i) <;> simp
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [lnn (va _ _ _), lnn (vo _ _), lo _ (by unfold ca; omega), lo _ (by unfold co; omega),
          c_a (by omega) (by omega) (by omega) (by omega), c_o (by omega) (by omega) (by omega)]
        cases T (fx u i) <;> simp <;> omega
  · simp only [List.mem_flatMap] at hc
    obtain ⟨⟨i1, i2⟩, hp, hc⟩ := hc
    simp only [pairsN, List.mem_filter, decide_eq_true_eq] at hp
    have hp' := mem_pairs8.mp hp.1
    have f1 := fxN h.n56 hu (show i1 < n by omega); have f2 := fxN h.n56 hu hp.2
    have hle := h.le u hu
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [lnn (vs _), lnn (vs _), lnn (vs _), lpp (vo _ _), lo _ (by unfold cs; omega), lo _ (by unfold cs; omega),
        lo _ (by unfold cs; omega), lo _ (by unfold co; omega), c_s (by omega), c_s (by omega), c_s (by omega),
        c_o (by omega) (by omega) (by omega)]
      cases h0 : T u <;> cases h1 : T (fx u i1) <;> cases h2 : T (fx u i2) <;> simp
      obtain ⟨i, _, _, hl⟩ := h.lvl u hu i1 i2 hp'.1 hp.2 h0 h1 h2
      omega
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j0, hj0, rfl⟩ := hc
      simp only [clauseTrue, List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [lnn (vs _), lnn (vs _), lnn (vs _), lo _ (by unfold cs; omega), lo _ (by unfold cs; omega),
        lo _ (by unfold cs; omega), c_s (by omega), c_s (by omega), c_s (by omega)]
      cases h0 : T u <;> cases h1 : T (fx u i1) <;> cases h2 : T (fx u i2) <;> simp
      obtain ⟨i, hi, hsi, hl⟩ := h.lvl u hu i1 i2 hp'.1 hp.2 h0 h1 h2
      by_cases hj : j0 + 1 < 64 ∧ j0 + 2 ≤ ℓ u
      · left
        refine ⟨pos (co u (j0 + 2)), ⟨hj.1, rfl⟩, ?_⟩
        rw [lpp (vo _ _), lo _ (by unfold co; omega), c_o (by omega) (by omega) (by omega)]; simp; omega
      · right
        have hf := fxN h.n56 hu hi
        refine ⟨i, hi, ?_⟩
        rw [lpp (va _ _ _), lo _ (by unfold ca; omega), c_a (by omega) (by omega) (by omega) (by omega)]
        simp [hsi]; omega

theorem units_ok {n : Nat} (h : Hyp n T ℓ) (ctrs : List (List Int × Nat)) (units : List (Nat × Bool))
    (hu : ∀ p ∈ units, p.1 < 2 ^ n ∧ T p.1 = p.2) : ∀ c ∈ cUnits units, clauseTrue (tc T ℓ ctrs) c = true := by
  intro c hc
  simp only [cUnits, List.mem_map] at hc
  obtain ⟨⟨u, bb⟩, hm, rfl⟩ := hc
  obtain ⟨hu1, hu2⟩ := hu _ hm
  have h64 := pow_le64 h.n56
  have vs : 0 < cs u := by unfold cs; omega
  simp only at hu1 hu2
  have e := c_s (T := T) (ℓ := ℓ) (u := u) (by omega)
  rw [← tc_lo (ctrs := ctrs) (by unfold cs cbase; omega)] at e
  cases bb <;> simp [clauseTrue, lpp vs, lnn vs, e, hu2]

theorem blk_ok {n : Nat} (h : Hyp n T ℓ) (ctrs : List (List Int × Nat)) (blocks : List Nat)
    (hb : ∀ R ∈ blocks, ∃ u, u < 2 ^ n ∧ T u ≠ R.testBit u) : ∀ c ∈ cBlk n blocks, clauseTrue (tc T ℓ ctrs) c = true := by
  intro c hc
  simp only [cBlk, List.mem_map] at hc
  obtain ⟨R, hR, rfl⟩ := hc
  obtain ⟨u, hu, hne⟩ := hb R hR
  have h64 := pow_le64 h.n56
  have vs : 0 < cs u := by unfold cs; omega
  have e := c_s (T := T) (ℓ := ℓ) (u := u) (by omega)
  rw [← tc_lo (ctrs := ctrs) (by unfold cs cbase; omega)] at e
  rw [clauseTrue, List.any_eq_true]
  refine ⟨if R.testBit u then neg (cs u) else pos (cs u), List.mem_map.mpr ⟨u, List.mem_range.mpr hu, rfl⟩, ?_⟩
  cases hr : R.testBit u <;> simp [lpp vs, lnn vs, e] <;> simp_all

theorem ctrVal_cons (b : Nat) (xs : List Int) (k : Nat) (rest : List (List Int × Nat)) (v : Nat) :
    ctrVal T ℓ b ((xs, k) :: rest) v =
      if v < b + 64 * k then decide ((v - b) % k + 1 ≤ cl (tc0 T ℓ) xs ((v - b) / k + 1))
      else ctrVal T ℓ (b + 64 * k) rest v := rfl

/-- counter blocks from base `b` -/
theorem ctrs_ok (τ : Nat → Bool) : ∀ (ctrs : List (List Int × Nat)) (b : Nat), cbase ≤ b →
    (∀ v, b ≤ v → τ v = ctrVal T ℓ b ctrs v) → (∀ v, v < cbase → τ v = tc0 T ℓ v) →
    (∀ p ∈ ctrs, 1 ≤ p.2 ∧ p.1.length ≤ 64 ∧ (∀ l ∈ p.1, l ≠ 0 ∧ l.natAbs < cbase) ∧
      cl (tc0 T ℓ) p.1 p.1.length ≤ p.2) →
    ∀ c ∈ cCtrs b ctrs, clauseTrue τ c = true
  | [], _, _, _, _, _, c, hc => by simp [cCtrs] at hc
  | (xs, k) :: rest, b, hb, hv, hlo, hp, c, hc => by
    unfold cCtrs at hc
    obtain ⟨hk, hlen, hlit, hcnt⟩ := hp (xs, k) (by simp)
    have hcl : ∀ i, cl τ xs i = cl (tc0 T ℓ) xs i := by
      intro i; unfold cl; congr 1; apply List.filter_congr; intro l hl
      have := (hlit l (List.mem_of_mem_take hl)).2
      unfold litTrue; split
      · rw [hlo _ (by omega)]
      · rw [hlo _ (by omega)]
    rcases List.mem_append.mp hc with hc | hc
    · refine atMost_sound τ b k xs hk (by unfold cbase at hb; omega) (fun l hl => (hlit l hl).1) ?_ (by rw [hcl]; exact hcnt) c hc
      intro i j hi1 hi hj1 hj
      have hblk := Dim8Lift.Cube.lt_block (K := k) (N := 64) (by omega) hi1 (Nat.le_trans hi hlen) hj1 hj
      have hd := Dim8Lift.Cube.regdec i j k (by omega) hj1 hj
      rw [hv _ (by unfold reg; omega), hcl, ctrVal_cons]
      unfold reg
      rw [if_pos (by omega), show b + (i - 1) * k + (j - 1) - b = (i - 1) * k + (j - 1) by omega, hd.1, hd.2,
        show j - 1 + 1 = j by omega, show i - 1 + 1 = i by omega]
    · exact ctrs_ok τ rest (b + 64 * k) (by omega) (by
        intro v hv'
        rw [hv v (by omega), ctrVal_cons, if_neg (by omega)]) hlo (fun p hp' => hp p (by simp [hp'])) c hc

theorem cover_bridge {n : Nat} (h : Hyp n T ℓ) (units : List (Nat × Bool)) (ctrs : List (List Int × Nat))
    (blocks : List Nat) (hu : ∀ p ∈ units, p.1 < 2 ^ n ∧ T p.1 = p.2)
    (hc : ∀ p ∈ ctrs, 1 ≤ p.2 ∧ p.1.length ≤ 64 ∧ (∀ l ∈ p.1, l ≠ 0 ∧ l.natAbs < cbase) ∧
      cl (tc0 T ℓ) p.1 p.1.length ≤ p.2)
    (hb : ∀ R ∈ blocks, ∃ u, u < 2 ^ n ∧ T u ≠ R.testBit u) :
    cnfTrue (tc T ℓ ctrs) (coverCnf n units ctrs blocks) = true := by
  unfold cnfTrue coverCnf
  rw [List.all_eq_true]
  intro c hcm
  simp only [List.mem_append] at hcm
  rcases hcm with (((h1 | h1) | h1) | h1) | h1
  · exact units_ok h ctrs units hu c h1
  · exact deg_ok h ctrs c h1
  · exact lvl_ok h ctrs c h1
  · exact ctrs_ok (tc T ℓ ctrs) ctrs cbase (Nat.le_refl _)
      (fun v hv => by unfold tc; rw [if_neg (by omega)]) (fun v hv => tc_lo hv) hc c h1
  · exact blk_ok h ctrs blocks hb c h1

/-- **Cover lemma.** If the cover CNF is unsatisfiable, a set satisfying the hypotheses agrees with one of
the blocked sets on all of Q_n. -/
theorem cover_of_unsat {n : Nat} (h : Hyp n T ℓ) {units : List (Nat × Bool)} {ctrs : List (List Int × Nat)}
    {blocks : List Nat} (hU : Unsat (coverCnf n units ctrs blocks)) (hu : ∀ p ∈ units, p.1 < 2 ^ n ∧ T p.1 = p.2)
    (hc : ∀ p ∈ ctrs, 1 ≤ p.2 ∧ p.1.length ≤ 64 ∧ (∀ l ∈ p.1, l ≠ 0 ∧ l.natAbs < cbase) ∧
      cl (tc0 T ℓ) p.1 p.1.length ≤ p.2) :
    ∃ R ∈ blocks, ∀ u, u < 2 ^ n → T u = R.testBit u := by
  apply Classical.byContradiction
  intro hn
  have hb : ∀ R ∈ blocks, ∃ u, u < 2 ^ n ∧ T u ≠ R.testBit u := by
    intro R hR
    apply Classical.byContradiction; intro hx
    exact hn ⟨R, hR, fun u hu' => by
      apply Classical.byContradiction; intro hne; exact hx ⟨u, hu', hne⟩⟩
  have := cover_bridge h units ctrs blocks hu hc hb
  rw [hU] at this; exact absurd this (by simp)

end Dim8Lift.Cover

#print axioms Dim8Lift.Cover.cover_of_unsat
