import CoverDefs
/-! The cover statement `CoverOK`, from the table checks and the cover CNF UNSATs. -/
set_option linter.deprecated false
namespace Dim8Lift.Tab
open Dim8Lift Dim8Lift.Cnf Dim8Lift.Cube Dim8Lift.Cover Dim8Lift.Sym Snake9.LocalWindow

theorem applyW_append : ∀ (w w' : List Nat) (u : Nat), applyW (w ++ w') u = applyW w (applyW w' u)
  | [], _, _ => rfl
  | c :: w, w', u => by show gen c (applyW (w ++ w') u) = gen c (applyW w (applyW w' u)); rw [applyW_append w w' u]

/-- words of B_n generators preserve a predicate preserved by each generator -/
theorem word_pres (n : Nat) (P : Nat → Bool) (hP : ∀ c, c < 36 → inB n c = true → ∀ u, u < 256 → P (gen c u) = P u) :
    ∀ (w : List Nat), (∀ c ∈ w, c < 36 ∧ inB n c = true) → ∀ u, u < 256 → P (applyW w u) = P u
  | [], _, _, _ => rfl
  | c :: w, hw, u, hu => by
    show P (gen c (applyW w u)) = P u
    have h1 := hw c (by simp)
    rw [hP c h1.1 h1.2 _ (applyW_lt w (fun c' h' => (hw c' (by simp [h'])).1) u hu),
      word_pres n P hP w (fun c' h' => hw c' (by simp [h'])) u hu]

theorem cnt_pres (w : List Nat) (hw : ∀ c ∈ w, c < 36) (S P : Nat → Bool)
    (hP : ∀ u, u < 256 → P (applyW w u) = P u) :
    cnt 256 (fun u => S (applyW w u) && P u) = cnt 256 (fun u => S u && P u) := by
  rw [← cnt_word w hw (fun v => S v && P v)]
  unfold cnt; apply sm_congr; intro u hu; simp only [hP u hu]

/-- the hypotheses of the cover bridge, for the part of a Pit inside Q_n (n = 5, 6) -/
theorem hyp_of_pit {L : Nat} {S : Nat → Bool} {ℓ : Nat → Nat} (hp : Pit 13 L 64 S ℓ) {n : Nat} (hn : n = 5 ∨ n = 6) :
    Hyp n S ℓ := by
  have h64 := pow_le64 hn
  have hn6 : n ≤ 6 := by rcases hn with rfl | rfl <;> omega
  refine ⟨hn, fun u hu => hp.lvl_le u (by omega), ?_, ?_⟩
  · intro u hu a b c hab hbc hc h0 h1 h2
    exact hp.deg u (by omega) a b c hab hbc (by omega) h0 h1 h2
  · intro u hu i1 i2 h12 h2n h0 h1 h2
    have htwo : twoB S u = true := (twoB_iff S u).mpr ⟨i1, i2, h12, by omega, h1, h2⟩
    obtain ⟨d, hd8, hsd, hl⟩ := hp.lvl u (by omega) htwo
    by_cases e1 : d = i1
    · subst e1; exact ⟨d, by omega, hsd, hl⟩
    · by_cases e2 : d = i2
      · subst e2; exact ⟨d, h2n, hsd, hl⟩
      · exact absurd (deg3 hp (by omega) (show i1 < 8 by omega) (show i2 < 8 by omega) hd8 (by omega)
          (Ne.symm e1) (Ne.symm e2) h0 h1 h2 hsd) id

theorem lits_count (f : Nat → Int) (g : Nat → Bool) (τ : Nat → Bool) (hf : ∀ u, u < 32 → litTrue τ (f u) = g u) :
    cl τ ((List.range 32).map f) ((List.range 32).map f).length = cnt 32 g := by
  rw [List.length_map, List.length_range]
  unfold cl; rw [List.take_of_length_le (by simp)]
  have : ∀ n, n ≤ 32 → (((List.range n).map f).filter (litTrue τ)).length = cnt n g := by
    intro n; induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.filter_append, List.length_append, ih (by omega), cnt_succ]
      simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, hf n (by omega)]
      cases g n <;> simp
  exact this 32 (Nat.le_refl _)

theorem cnt_lt (S : Nat → Bool) (n : Nat) : ∀ N, n ≤ N → cnt N (fun u => S u && decide (u < n)) = cnt n S := by
  intro N
  induction N with
  | zero => intro h; have : n = 0 := by omega
            subst this; rfl
  | succ N ih =>
    intro h
    by_cases e : n = N + 1
    · subst e; unfold cnt; apply sm_congr; intro t ht; simp [ht]
    · rw [cnt_succ, ih (by omega)]; simp; omega

theorem cnt_add (f : Nat → Bool) (a : Nat) : ∀ b, cnt (a + b) f = cnt a f + cnt b (fun u => f (a + u)) := by
  intro b; induction b with
  | zero => rfl
  | succ b ih => rw [show a + (b + 1) = (a + b) + 1 by omega, cnt_succ, ih, cnt_succ]; omega

theorem cnt_split' (n : Nat) (p : Nat → Bool) : cnt n p + cnt n (fun t => !p t) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cnt_succ, cnt_succ]; cases p n <;> simp <;> omega

theorem gen_lt36 {n c : Nat} (h : inB n c = true) (hn : n ≤ 8) : c < 36 := by
  unfold inB at h; simp at h; omega

theorem coverOK_of {L : Nat} (t5 : List (Nat × List Nat × Nat)) (t6 : List (Nat × Nat × List Nat × Nat))
    (reps : List (Nat × Nat))
    (h5 : t5.all (fun e => chk 5 e.1 e.2.1 e.2.2) = true)
    (h6 : t6.all (fun e => chk 6 e.2.1 e.2.2.1 e.2.2.2 && reps.contains (pcN 64 e.2.2.2, e.2.2.2)) = true)
    (hU5 : Unsat (c5Cnf (t5.map (·.1))))
    (hU6 : ∀ e ∈ t5, Unsat (c6Cnf e.2.2 ((t6.filter (·.1 == e.2.2)).map (·.2.1)))) :
    CoverOK L reps := by
  intro S ℓ k hp hk hm hc
  -- the two halves of copy 0 along coordinate 5
  have hsplit : ∀ T : Nat → Bool, cnt 256 (fun u => T u && decide (u < 64)) =
      cnt 256 (fun u => T u && decide (u < 32)) + cnt 256 (fun u => T u && decide (32 ≤ u ∧ u < 64)) := by
    intro T; unfold cnt; rw [← sm_add]; apply sm_congr; intro u _
    by_cases h1 : u < 32
    · have : u < 64 := by omega
      have h3 : ¬ 32 ≤ u := by omega
      cases hT : T u <;> simp [hT, h1, this, h3]
    · by_cases h2 : u < 64
      · have h3 : 32 ≤ u := by omega
        cases hT : T u <;> simp [hT, h1, h2, h3]
      · cases hT : T u <;> simp [hT, h1, h2]
  -- step 1: flip coordinate 5 if the upper half is larger
  obtain ⟨w0, hw0, hw0b, hge, hsum⟩ : ∃ w0 : List Nat, (∀ c ∈ w0, c < 36) ∧ (∀ c ∈ w0, c < 36 ∧ inB 6 c = true) ∧
      cnt 256 (fun u => S (applyW w0 u) && decide (32 ≤ u ∧ u < 64)) ≤ cnt 256 (fun u => S (applyW w0 u) && decide (u < 32)) ∧
      cnt 256 (fun u => S (applyW w0 u) && decide (u < 64)) = k := by
    by_cases hle : cnt 256 (fun u => S u && decide (32 ≤ u ∧ u < 64)) ≤ cnt 256 (fun u => S u && decide (u < 32))
    · exact ⟨[], by simp, by simp, hle, hc⟩
    · refine ⟨[33], by simp, by simp [inB], ?_, ?_⟩
      · have e1 : cnt 256 (fun u => S (applyW [33] u) && decide (u < 32)) = cnt 256 (fun u => S u && decide (32 ≤ u ∧ u < 64)) := by
          rw [← cnt_perm (c := 33) (by omega) (fun v => S v && decide (32 ≤ v ∧ v < 64))]
          unfold cnt; apply sm_congr; intro u hu
          have := (flip5_F ⟨gen 33 u, gen_lt (by omega) hu⟩).1
          simp only [gen_gen (show 33 < 36 by omega) hu] at this
          simp only [applyW, this] <;> rfl
        have e2 : cnt 256 (fun u => S (applyW [33] u) && decide (32 ≤ u ∧ u < 64)) = cnt 256 (fun u => S u && decide (u < 32)) := by
          rw [← cnt_perm (c := 33) (by omega) (fun v => S v && decide (v < 32))]
          unfold cnt; apply sm_congr; intro u hu
          have := (flip5_F ⟨u, hu⟩).1
          simp only [applyW, this] <;> rfl
        rw [e1, e2]; exact Nat.le_of_lt (Nat.lt_of_not_le hle)
      · rw [← hc]
        rw [← cnt_perm (c := 33) (by omega) (fun v => S v && decide (v < 64))]
        unfold cnt; apply sm_congr; intro u hu
        have := (flip5_F ⟨u, hu⟩).2
        simp only [applyW, this] <;> rfl
  -- S1
  have hp1 := pit_word w0 hw0 hp
  have H5 := hyp_of_pit hp1 (n := 5) (Or.inl rfl)
  have h0eq : cnt 256 (fun u => S (applyW w0 u) && decide (u < 32)) = cnt 32 (fun u => S (applyW w0 u)) :=
    cnt_lt _ 32 256 (by omega)
  have hk1 := hsplit (fun u => S (applyW w0 u))
  -- step 2: Q5 cover
  obtain ⟨R, hR, hRS⟩ := cover_of_unsat H5 hU5 (units := []) (by simp) (by
    intro p hp'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    subst hp'
    refine ⟨by decide, by simp [unsel5], ?_, ?_⟩
    · intro l hl
      simp only [unsel5, List.mem_map, List.mem_range] at hl
      obtain ⟨u, hu, rfl⟩ := hl
      simp [neg, cs, Cover.cbase]; omega
    · unfold unsel5
      rw [lits_count (fun u => neg (cs u)) (fun u => !S (applyW w0 u)) _ (by
        intro u hu; rw [lnn (by unfold cs; omega), c_s (by omega)])]
      have := cnt_split' 32 (fun u => S (applyW w0 u))
      omega)
  obtain ⟨e5, he5, rfl⟩ := List.mem_map.mp hR
  have hc5 := List.all_eq_true.mp h5 e5 he5
  unfold chk at hc5
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq] at hc5
  obtain ⟨hw5, hc5⟩ := hc5
  have hw5' : ∀ c ∈ e5.2.1, c < 36 ∧ inB 5 c = true := fun c h => ⟨gen_lt36 (hw5 c h) (by omega), hw5 c h⟩
  have hw5'' : ∀ c ∈ e5.2.1, c < 36 := fun c h => (hw5' c h).1
  -- S2 = S1 ∘ w5 has the representative r5 on the low half
  have hS2 : ∀ u, u < 32 → S (applyW w0 (applyW e5.2.1 u)) = e5.2.2.testBit u := by
    intro u hu
    have := hc5 u (by simpa using hu)
    rw [hRS _ (by simpa using this.1), this.2]
  have hp2 := pit_word e5.2.1 hw5'' hp1
  have H6 := hyp_of_pit hp2 (n := 6) (Or.inr rfl)
  -- predicates preserved by the B5 word
  have p32 : ∀ u, u < 256 → decide (applyW e5.2.1 u < 32) = decide (u < 32) :=
    word_pres 5 (fun v => decide (v < 32)) (fun c hc hb u hu => (pres5_F ⟨c, hc⟩ hb ⟨u, hu⟩).1) _ hw5'
  have p64 : ∀ u, u < 256 → decide (applyW e5.2.1 u < 64) = decide (u < 64) :=
    word_pres 5 (fun v => decide (v < 64)) (fun c hc hb u hu => (pres5_F ⟨c, hc⟩ hb ⟨u, hu⟩).2) _ hw5'
  have pmid : ∀ u, u < 256 → decide (32 ≤ applyW e5.2.1 u ∧ applyW e5.2.1 u < 64) = decide (32 ≤ u ∧ u < 64) := by
    intro u hu; have a1 := p32 u hu; have a2 := p64 u hu
    simp only [decide_eq_decide] at a1 a2 ⊢; omega
  let S2 : Nat → Bool := fun u => S (applyW w0 (applyW e5.2.1 u))
  let ℓ' : Nat → Nat := fun u => ℓ (applyW w0 (applyW e5.2.1 u))
  have q0 : cnt 256 (fun u => S2 u && decide (u < 32)) = cnt 256 (fun u => S (applyW w0 u) && decide (u < 32)) :=
    cnt_pres e5.2.1 hw5'' (fun v => S (applyW w0 v)) (fun v => decide (v < 32)) p32
  have q1 : cnt 256 (fun u => S2 u && decide (32 ≤ u ∧ u < 64)) =
      cnt 256 (fun u => S (applyW w0 u) && decide (32 ≤ u ∧ u < 64)) :=
    cnt_pres e5.2.1 hw5'' (fun v => S (applyW w0 v)) (fun v => decide (32 ≤ v ∧ v < 64)) pmid
  have qk : cnt 256 (fun u => S2 u && decide (u < 64)) = k := by
    rw [← hsum]; exact cnt_pres e5.2.1 hw5'' (fun v => S (applyW w0 v)) (fun v => decide (v < 64)) p64
  have hpc : pcN 32 e5.2.2 = cnt 32 S2 := by
    unfold pcN cnt; apply sm_congr; intro u hu; simp only [S2, hS2 u hu]
  have hlo : cnt 256 (fun u => S2 u && decide (u < 32)) = cnt 32 S2 := cnt_lt S2 32 256 (by omega)
  have h64 : cnt 256 (fun u => S2 u && decide (u < 64)) = cnt 64 S2 := cnt_lt S2 64 256 (by omega)
  have hadd : cnt 64 S2 = cnt 32 S2 + cnt 32 (fun u => S2 (32 + u)) := cnt_add S2 32 32
  have hs2 := hsplit S2
  have hsel : cl (tc0 S2 ℓ') selB selB.length = cnt 32 (fun u => S2 (32 + u)) := by
    unfold selB
    exact lits_count (fun u => pos (cs (32 + u))) (fun u => S2 (32 + u)) _ (by
      intro u hu; rw [lpp (by unfold cs; omega), c_s (by omega)])
  have hunsel : cl (tc0 S2 ℓ') unselB unselB.length = cnt 32 (fun u => !S2 (32 + u)) := by
    unfold unselB
    exact lits_count (fun u => neg (cs (32 + u))) (fun u => !S2 (32 + u)) _ (by
      intro u hu; rw [lnn (by unfold cs; omega), c_s (by omega)])
  have hsp := cnt_split' 32 (fun u => S2 (32 + u))
  obtain ⟨R6, hR6, hR6S⟩ := cover_of_unsat (T := S2) (ℓ := ℓ') H6 (hU6 e5 he5) (by
      intro p hp'
      simp only [List.mem_map, List.mem_range] at hp'
      obtain ⟨u, hu, rfl⟩ := hp'
      exact ⟨by simp; omega, hS2 u hu⟩) (by
      intro p hp'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
      have hl : ∀ l ∈ selB ++ unselB, l ≠ 0 ∧ l.natAbs < Cover.cbase := by
        intro l hl
        simp only [selB, unselB, List.mem_append, List.mem_map, List.mem_range] at hl
        rcases hl with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [pos, neg, cs, Cover.cbase] <;> omega
      rcases hp' with rfl | rfl
      · refine ⟨by omega, by simp [selB], fun l h => hl l (List.mem_append_left _ h), ?_⟩
        show cl (tc0 S2 ℓ') selB selB.length ≤ pcN 32 e5.2.2
        rw [hsel, hpc]; omega
      · refine ⟨by omega, by simp [unselB], fun l h => hl l (List.mem_append_right _ h), ?_⟩
        show cl (tc0 S2 ℓ') unselB unselB.length ≤ 32 - (29 - pcN 32 e5.2.2)
        rw [hunsel, hpc]; omega)
  obtain ⟨e6, he6, rfl⟩ := List.mem_map.mp hR6
  have he6t := (List.mem_filter.mp he6).1
  have hc6 := List.all_eq_true.mp h6 e6 he6t
  simp only [Bool.and_eq_true] at hc6
  obtain ⟨hc6, hrep⟩ := hc6
  unfold chk at hc6
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq] at hc6
  obtain ⟨hw6, hc6⟩ := hc6
  have hw6' : ∀ c ∈ e6.2.2.1, c < 36 ∧ inB 6 c = true := fun c h => ⟨gen_lt36 (hw6 c h) (by omega), hw6 c h⟩
  have hw6'' : ∀ c ∈ e6.2.2.1, c < 36 := fun c h => (hw6' c h).1
  have p64' : ∀ u, u < 256 → decide (applyW e6.2.2.1 u < 64) = decide (u < 64) :=
    word_pres 6 (fun v => decide (v < 64)) (fun c hc hb u hu => pres6_F ⟨c, hc⟩ hb ⟨u, hu⟩) _ hw6'
  have hS3 : ∀ u, u < 64 → S2 (applyW e6.2.2.1 u) = e6.2.2.2.testBit u := by
    intro u hu
    have := hc6 u (by simpa using hu)
    rw [hR6S _ (by simpa using this.1), this.2]
  -- the size of the representative is k
  have hk3 : cnt 256 (fun u => S2 (applyW e6.2.2.1 u) && decide (u < 64)) = k := by
    rw [← qk]; exact cnt_pres e6.2.2.1 hw6'' S2 (fun v => decide (v < 64)) p64'
  have hk4 : cnt 256 (fun u => S2 (applyW e6.2.2.1 u) && decide (u < 64)) = pcN 64 e6.2.2.2 := by
    rw [cnt_lt _ 64 256 (by omega)]
    unfold pcN cnt; apply sm_congr; intro u hu; simp only [hS3 u hu]
  refine ⟨w0 ++ e5.2.1 ++ e6.2.2.1, ?_, (pcN 64 e6.2.2.2, e6.2.2.2), ?_, by simp; omega, ?_⟩
  · intro c hc
    simp only [List.mem_append] at hc
    rcases hc with (h | h) | h
    · exact hw0 c h
    · exact hw5'' c h
    · exact hw6'' c h
  · simpa using hrep
  · intro u hu
    rw [applyW_append, applyW_append]
    exact hS3 u hu

end Dim8Lift.Tab
#print axioms Dim8Lift.Tab.coverOK_of
