/-
Transport lemmas for the direction-aware automaton.

The kernel-checked table `step_table` covers canonical direction windows only.
These lemmas show that every quantity in the step test is invariant under
relabelling the directions, so the table applies to an arbitrary window.
Core Lean only.
-/
import WindowAutomatonData

namespace Snake9.WindowAutomaton

/-! ### `idx` -/

theorem idx_le_length (l : List Nat) (d : Nat) : idx l d ≤ l.length := by
  induction l with
  | nil => simp [idx]
  | cons a l ih => unfold idx; split <;> simp <;> omega

theorem idx_of_not_mem (l : List Nat) (d : Nat) (h : d ∉ l) : idx l d = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at h
    unfold idx
    rw [if_neg (Ne.symm h.1), ih h.2]
    rfl

theorem idx_lt_of_mem (l : List Nat) (d : Nat) (h : d ∈ l) : idx l d < l.length := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    unfold idx
    split
    · simp
    · rename_i hne
      have : d ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hne
        · exact h
      simp
      exact ih this

theorem idx_append_of_mem (l l' : List Nat) (d : Nat) (h : d ∈ l) : idx (l ++ l') d = idx l d := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.cons_append]
    unfold idx
    split
    · rfl
    · rename_i hne
      have : d ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hne
        · exact h
      rw [ih this]

theorem idx_append_of_not_mem (l l' : List Nat) (d : Nat) (h : d ∉ l) :
    idx (l ++ l') d = l.length + idx l' d := by
  induction l with
  | nil => simp [idx]
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at h
    show (if a = d then 0 else idx (l ++ l') d + 1) = (a :: l).length + idx l' d
    rw [if_neg (Ne.symm h.1), ih h.2]
    simp only [List.length_cons]
    omega

/-- `idx` returns a first index, so equal indices of members force equal members. -/
theorem idx_inj (l : List Nat) (a b : Nat) (ha : a ∈ l) (hb : b ∈ l) (h : idx l a = idx l b) :
    a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    unfold idx at h
    by_cases hxa : x = a <;> by_cases hxb : x = b
    · omega
    · rw [if_pos hxa, if_neg hxb] at h; omega
    · rw [if_neg hxa, if_pos hxb] at h; omega
    · rw [if_neg hxa, if_neg hxb] at h
      have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h' | h'
        · exact absurd h'.symm hxa
        · exact h'
      have hb' : b ∈ l := by
        rcases List.mem_cons.mp hb with h' | h'
        · exact absurd h'.symm hxb
        · exact h'
      exact ih ha' hb' (by omega)

theorem idx_map (σ : Nat → Nat) (l : List Nat) (d : Nat)
    (hinj : ∀ b ∈ l, σ b = σ d → b = d) : idx (l.map σ) (σ d) = idx l d := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    unfold idx
    by_cases hd : a = d
    · subst hd; simp
    · have hne : σ a ≠ σ d := fun h => hd (hinj a (List.mem_cons_self) h)
      rw [if_neg hne, if_neg hd, ih (fun b hb => hinj b (List.mem_cons_of_mem _ hb))]

theorem mem_map_inj (σ : Nat → Nat) (l : List Nat) (d : Nat)
    (hinj : ∀ b ∈ l, σ b = σ d → b = d) : (σ d ∈ l.map σ) ↔ d ∈ l := by
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := List.mem_map.mp h
    exact hinj b hb he ▸ hb
  · intro h
    exact List.mem_map.mpr ⟨d, h, rfl⟩

/-! ### `seenAfter` -/

theorem seenAfter_append : ∀ (seen ds : List Nat), ∃ r, seenAfter seen ds = seen ++ r
  | seen, [] => ⟨[], by simp [seenAfter]⟩
  | seen, d :: ds => by
    unfold seenAfter
    split
    · exact seenAfter_append seen ds
    · obtain ⟨r, hr⟩ := seenAfter_append (seen ++ [d]) ds
      exact ⟨d :: r, by rw [hr]; simp⟩

theorem mem_seenAfter_of_mem_seen : ∀ (seen ds : List Nat) (d : Nat), d ∈ seen → d ∈ seenAfter seen ds
  | seen, [], d, h => h
  | seen, e :: ds, d, h => by
    unfold seenAfter
    split
    · exact mem_seenAfter_of_mem_seen seen ds d h
    · exact mem_seenAfter_of_mem_seen _ ds d (List.mem_append_left _ h)

theorem mem_seenAfter : ∀ (seen ds : List Nat) (d : Nat), d ∈ ds → d ∈ seenAfter seen ds
  | seen, [], d, h => by simp at h
  | seen, e :: ds, d, h => by
    rcases List.mem_cons.mp h with rfl | h
    · unfold seenAfter
      split
      · exact mem_seenAfter_of_mem_seen seen ds d (by assumption)
      · exact mem_seenAfter_of_mem_seen _ ds d (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · unfold seenAfter
      split <;> exact mem_seenAfter _ ds d h

/-! ### `canonGo` as a map -/

theorem canonGo_eq_map : ∀ (seen ds : List Nat), canonGo seen ds = ds.map (idx (seenAfter seen ds))
  | seen, [] => rfl
  | seen, d :: ds => by
    simp only [canonGo, seenAfter, List.map_cons]
    rw [canonGo_eq_map]
    congr 1
    -- idx seen d = idx (seenAfter seen' ds) d, where d ∈ seen'
    obtain ⟨r, hr⟩ := seenAfter_append (if d ∈ seen then seen else seen ++ [d]) ds
    rw [hr]
    split
    · rename_i hmem
      rw [idx_append_of_mem _ _ _ hmem]
    · rename_i hnot
      rw [List.append_assoc, idx_append_of_not_mem _ _ _ hnot, idx_of_not_mem _ _ hnot]
      simp [idx]

theorem length_canonGo : ∀ (seen ds : List Nat), (canonGo seen ds).length = ds.length
  | seen, [] => rfl
  | seen, d :: ds => by simp [canonGo, length_canonGo]

theorem length_canon (ds : List Nat) : (canon ds).length = ds.length := length_canonGo [] ds

/-- The labelling map of a direction list. -/
def label (ds : List Nat) : Nat → Nat := idx (seenAfter [] ds)

theorem canon_eq_map (ds : List Nat) : canon ds = ds.map (label ds) := canonGo_eq_map [] ds

theorem label_inj (ds : List Nat) : ∀ a ∈ ds, ∀ b ∈ ds, label ds a = label ds b → a = b :=
  fun a ha b hb h => idx_inj _ a b (mem_seenAfter [] ds a ha) (mem_seenAfter [] ds b hb) h

/-! ### `canonGo` is invariant under injective relabelling -/

theorem canonGo_map (σ : Nat → Nat) : ∀ (seen ds : List Nat),
    (∀ a ∈ seen ++ ds, ∀ b ∈ seen ++ ds, σ a = σ b → a = b) →
    canonGo (seen.map σ) (ds.map σ) = canonGo seen ds
  | seen, [], _ => rfl
  | seen, d :: ds, hinj => by
    have hd : d ∈ seen ++ d :: ds := List.mem_append_right _ (List.mem_cons_self)
    have hseen : ∀ b ∈ seen, σ b = σ d → b = d :=
      fun b hb h => hinj b (List.mem_append_left _ hb) d hd h
    simp only [List.map_cons, canonGo]
    rw [idx_map σ seen d hseen]
    congr 1
    have hif : (if σ d ∈ seen.map σ then seen.map σ else seen.map σ ++ [σ d]) =
        (if d ∈ seen then seen else seen ++ [d]).map σ := by
      by_cases hm : d ∈ seen
      · rw [if_pos hm, if_pos ((mem_map_inj σ seen d hseen).mpr hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((mem_map_inj σ seen d hseen).mp h)), List.map_append]
        rfl
    rw [hif]
    apply canonGo_map σ
    intro a ha b hb h
    apply hinj a _ b _ h
    · rcases List.mem_append.mp ha with ha | ha
      · split at ha
        · exact List.mem_append_left _ ha
        · rcases List.mem_append.mp ha with ha | ha
          · exact List.mem_append_left _ ha
          · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp ha)))
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
    · rcases List.mem_append.mp hb with hb | hb
      · split at hb
        · exact List.mem_append_left _ hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact List.mem_append_left _ hb
          · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hb)))
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)

theorem canon_map (σ : Nat → Nat) (ds : List Nat)
    (hinj : ∀ a ∈ ds, ∀ b ∈ ds, σ a = σ b → a = b) : canon (ds.map σ) = canon ds :=
  canonGo_map σ [] ds (by simpa using hinj)

/-- Injectivity of the labelling restricted to a sub-list. -/
theorem label_inj_sub (ds sub : List Nat) (hsub : ∀ x ∈ sub, x ∈ ds) :
    ∀ a ∈ sub, ∀ b ∈ sub, label ds a = label ds b → a = b :=
  fun a ha b hb h => label_inj ds a (hsub a ha) b (hsub b hb) h

theorem canon_canon_drop (ds : List Nat) (n : Nat) : canon ((canon ds).drop n) = canon (ds.drop n) := by
  rw [canon_eq_map ds, ← List.map_drop]
  exact canon_map _ _ (label_inj_sub ds _ (fun x hx => List.drop_subset n ds hx))

theorem canon_canon_take (ds : List Nat) (n : Nat) : canon ((canon ds).take n) = canon (ds.take n) := by
  rw [canon_eq_map ds, ← List.map_take]
  exact canon_map _ _ (label_inj_sub ds _ (fun x hx => List.take_subset n ds hx))

theorem canon_canon_drop_reverse (ds : List Nat) (n : Nat) :
    canon ((canon ds).drop n).reverse = canon (ds.drop n).reverse := by
  rw [canon_eq_map ds, ← List.map_drop, ← List.map_reverse]
  exact canon_map _ _ (label_inj_sub ds _ (fun x hx => List.drop_subset n ds (List.mem_reverse.mp hx)))

/-! ### Restricted growth -/

theorem canonGo_isRGS : ∀ (seen ds : List Nat), isRGS (canonGo seen ds) seen.length = true
  | seen, [] => rfl
  | seen, d :: ds => by
    simp only [canonGo, isRGS, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨idx_le_length seen d, ?_⟩
    have key : (if seen.length < idx seen d + 1 then idx seen d + 1 else seen.length) =
        (if d ∈ seen then seen else seen ++ [d]).length := by
      by_cases hm : d ∈ seen
      · have := idx_lt_of_mem seen d hm
        rw [if_neg (by omega), if_pos hm]
      · rw [idx_of_not_mem seen d hm, if_pos (by omega), if_neg hm]
        simp
    rw [key]
    exact canonGo_isRGS _ ds

theorem canon_isRGS (ds : List Nat) : isRGS (canon ds) 0 = true := canonGo_isRGS [] ds

/-! ### `inducedPattern` is invariant under injective relabelling -/

theorem count_map_inj (σ : Nat → Nat) (l : List Nat) (d : Nat)
    (hinj : ∀ b ∈ l, σ b = σ d → b = d) : (l.map σ).count (σ d) = l.count d := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.count_cons]
    rw [ih (fun b hb => hinj b (List.mem_cons_of_mem _ hb))]
    congr 1
    by_cases h : a = d
    · subst h; simp
    · have : σ a ≠ σ d := fun he => h (hinj a (List.mem_cons_self) he)
      simp [h, this]

theorem firsts_map (σ : Nat → Nat) : ∀ (seen l : List Nat),
    (∀ a ∈ seen ++ l, ∀ b ∈ seen ++ l, σ a = σ b → a = b) →
    firsts (seen.map σ) (l.map σ) = (firsts seen l).map σ
  | seen, [], _ => by simp [firsts, List.map_reverse]
  | seen, d :: l, hinj => by
    have hd : d ∈ seen ++ d :: l := List.mem_append_right _ (List.mem_cons_self)
    have hseen : ∀ b ∈ seen, σ b = σ d → b = d :=
      fun b hb h => hinj b (List.mem_append_left _ hb) d hd h
    simp only [List.map_cons, firsts]
    have hif : (if σ d ∈ seen.map σ then seen.map σ else σ d :: seen.map σ) =
        (if d ∈ seen then seen else d :: seen).map σ := by
      by_cases hm : d ∈ seen
      · rw [if_pos hm, if_pos ((mem_map_inj σ seen d hseen).mpr hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((mem_map_inj σ seen d hseen).mp h))]
        rfl
    rw [hif]
    apply firsts_map σ
    intro a ha b hb h
    apply hinj a _ b _ h
    · rcases List.mem_append.mp ha with ha | ha
      · split at ha
        · exact List.mem_append_left _ ha
        · rcases List.mem_cons.mp ha with ha | ha
          · exact ha ▸ hd
          · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
    · rcases List.mem_append.mp hb with hb | hb
      · split at hb
        · exact List.mem_append_left _ hb
        · rcases List.mem_cons.mp hb with hb | hb
          · exact hb ▸ hd
          · exact List.mem_append_left _ hb
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)

theorem mem_firsts : ∀ (seen l : List Nat) (d : Nat), d ∈ firsts seen l → d ∈ seen ∨ d ∈ l
  | seen, [], d, h => Or.inl (by simpa [firsts] using h)
  | seen, e :: l, d, h => by
    simp only [firsts] at h
    rcases mem_firsts _ l d h with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem oddCount_map (σ : Nat → Nat) (seg : List Nat)
    (hinj : ∀ a ∈ seg, ∀ b ∈ seg, σ a = σ b → a = b) : oddCount (seg.map σ) = oddCount seg := by
  unfold oddCount
  have hf := firsts_map σ [] seg (by simpa using hinj)
  simp only [List.map_nil] at hf
  rw [hf, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro d hd
  have hd' : d ∈ seg := by
    rcases mem_firsts [] seg d hd with h | h
    · simp at h
    · exact h
  simp only [Function.comp]
  rw [count_map_inj σ seg d (fun b hb h => hinj b hb d hd' h)]

theorem blockOK_map (σ : Nat → Nat) (seg : List Nat)
    (hinj : ∀ a ∈ seg, ∀ b ∈ seg, σ a = σ b → a = b) : blockOK (seg.map σ) = blockOK seg := by
  unfold blockOK
  rw [oddCount_map σ seg hinj, List.length_map]

theorem prefixes_map (σ : Nat → Nat) : ∀ (l : List Nat),
    prefixes (l.map σ) = (prefixes l).map (List.map σ)
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, prefixes, prefixes_map σ l, List.map_map]
    rfl

theorem blocks_map (σ : Nat → Nat) : ∀ (l : List Nat), blocks (l.map σ) = (blocks l).map (List.map σ)
  | [] => rfl
  | a :: l => by
    have h1 : prefixes ((a :: l).map σ) = (prefixes (a :: l)).map (List.map σ) := prefixes_map σ (a :: l)
    simp only [List.map_cons] at h1
    simp only [List.map_cons, blocks, List.map_append, h1, blocks_map σ l]

theorem mem_prefixes_sub : ∀ (l seg : List Nat), seg ∈ prefixes l → ∀ x ∈ seg, x ∈ l
  | [], seg, h => by simp [prefixes] at h
  | a :: l, seg, h => by
    simp only [prefixes, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨p, hp, rfl⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact List.mem_cons_self
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_prefixes_sub l p hp x hx)

theorem mem_blocks_sub : ∀ (l seg : List Nat), seg ∈ blocks l → ∀ x ∈ seg, x ∈ l
  | [], seg, h => by simp [blocks] at h
  | a :: l, seg, h => by
    simp only [blocks, List.mem_append] at h
    rcases h with h | h
    · exact mem_prefixes_sub _ seg h
    · intro x hx; exact List.mem_cons_of_mem _ (mem_blocks_sub l seg h x hx)

theorem inducedPattern_map (σ : Nat → Nat) (ds : List Nat)
    (hinj : ∀ a ∈ ds, ∀ b ∈ ds, σ a = σ b → a = b) :
    inducedPattern (ds.map σ) = inducedPattern ds := by
  unfold inducedPattern
  rw [blocks_map, List.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Function.comp]
  constructor
  · intro h seg hseg
    rw [← blockOK_map σ seg (fun a ha b hb => hinj a (mem_blocks_sub ds seg hseg a ha) b
      (mem_blocks_sub ds seg hseg b hb))]
    exact h seg hseg
  · intro h seg hseg
    rw [blockOK_map σ seg (fun a ha b hb => hinj a (mem_blocks_sub ds seg hseg a ha) b
      (mem_blocks_sub ds seg hseg b hb))]
    exact h seg hseg

theorem inducedPattern_canon (ds : List Nat) : inducedPattern (canon ds) = inducedPattern ds := by
  rw [canon_eq_map]
  exact inducedPattern_map _ ds (label_inj ds)

/-! ### Transport of the step test -/

theorem wforb_canon_drop (ds syms : List Nat) (n : Nat) :
    wforb ((canon ds).drop n) syms = wforb (ds.drop n) syms := by
  unfold wforb wforb1
  rw [canon_canon_drop, canon_canon_drop_reverse]

theorem pot_canon_drop (ds t : List Nat) (n : Nat) : pot ((canon ds).drop n) t = pot (ds.drop n) t := by
  unfold pot
  rw [canon_canon_drop]

theorem pot_canon_take (ds t : List Nat) (n : Nat) : pot ((canon ds).take n) t = pot (ds.take n) t := by
  unfold pot
  rw [canon_canon_take]

theorem sym_ge_one (a : Nat) (h : 1 ≤ a) : 1 ≤ sym a := by unfold sym; split <;> omega
theorem sym_le_six (a : Nat) : sym a ≤ 6 := by unfold sym; split <;> omega
theorem sym_le (a : Nat) : sym a ≤ a := by unfold sym; split <;> omega

/-- The step inequality for an arbitrary seven-direction window. -/
theorem step_raw (x : List Nat) (hx : x.length = 7) (t1 t2 t3 s : Nat)
    (h1 : 1 ≤ t1) (h2 : 1 ≤ t2) (h3 : 1 ≤ t3) (hs : 1 ≤ s)
    (hind : inducedPattern x = true)
    (hw2 : wforb (x.drop 4) [sym t3, sym s] = false)
    (hw3 : wforb (x.drop 3) [sym t2, sym t3, sym s] = false)
    (hw4 : wforb (x.drop 2) [sym t1, sym t2, sym t3, sym s] = false) :
    10 + pot (x.drop 1) [sym t2, sym t3, sym s] ≤ 3 * sym s + pot (x.take 6) [sym t1, sym t2, sym t3] := by
  have hc := allRGS_spec 7 0 check step_table (canon x) (by rw [length_canon, hx]) (canon_isRGS x)
  unfold check at hc
  rw [inducedPattern_canon, hind] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  have h := allSym_spec _ (allSym_spec _ (allSym_spec _ (allSym_spec _ hc (sym t1) (sym_ge_one _ h1)
    (sym_le_six _)) (sym t2) (sym_ge_one _ h2) (sym_le_six _)) (sym t3) (sym_ge_one _ h3)
    (sym_le_six _)) (sym s) (sym_ge_one _ hs) (sym_le_six _)
  rw [wforb_canon_drop, wforb_canon_drop, wforb_canon_drop, hw2, hw3, hw4, pot_canon_drop,
    pot_canon_take] at h
  simpa using h

end Snake9.WindowAutomaton
