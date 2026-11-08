import Share185Blocks
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
/-! ### Totalizer kinds -/

theorem sublG_sublist {α : Type} [DecidableEq α] : ∀ {l m : List α}, sublG l m = true → l.Sublist m
  | [], _, _ => List.nil_sublist _
  | _ :: _, [], h => by simp [sublG] at h
  | a :: as, b :: bs, h => by
    unfold sublG at h
    by_cases hab : a = b
    · subst hab; simp only [if_true] at h; exact (sublG_sublist h).cons₂ a
    · simp only [hab, if_false] at h; exact (sublG_sublist h).cons b

theorem emp_total {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .emp q) :
    t.lits.countP (lv (baseS S E M X Mr)) ≤ emptyCount S q := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hs, hsub⟩ := h
  have : t.lits.countP (lv (baseS S E M X Mr)) = (t.lits.map (sqAB X)).countP (emptyPred S q) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro a ha
    obtain ⟨h1, h2⟩ := hs a ha
    rw [base_posSq h1, h2]; rfl
  rw [this]
  unfold emptyCount
  rw [← List.countP_eq_length_filter]
  exact (sublG_sublist hsub).countP_le

theorem nb_total {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .nb q) :
    t.lits.countP (lv (baseS S E M X Mr)) = cnt S (nbrs q) ∧ t.lits.length = 9 := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hp, hm, _⟩ := h
  constructor
  · unfold cnt
    rw [← List.countP_eq_length_filter, ← hm, List.countP_map]
    apply List.countP_congr
    intro a ha
    have hP : isP M (a / 2) = true := by
      have := hp a ha
      simp only [posP, Bool.and_eq_true] at this; exact this.2
    have hb : lv (baseS S E M X Mr) a = S (vl M a) := by
      rw [lv_congr (τ₂ := base S E M) (baseS_old (oldVar_of_isP hP))]
      exact base_posP (hp a ha)
    simp [hb]
  · have := congrArg List.length hm
    rw [List.length_map] at this
    rw [this]; rfl

theorem nb_pos {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .nb q) (hw : ∀ v ∈ w, S v = true) :
    1 ≤ cnt S (nbrs q) := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem, and_assoc] at h
  obtain ⟨_, _, _, v, hv, hvw⟩ := h
  unfold cnt
  rw [← List.countP_eq_length_filter]
  exact List.countP_pos_iff.2 ⟨v, hv, hw v hvw⟩

theorem sum_sublist_le : ∀ {l₁ l₂ : List Nat}, l₁.Sublist l₂ → l₁.sum ≤ l₂.sum
  | _, _, .slnil => Nat.le_refl _
  | _, _, .cons a h => by rw [List.sum_cons]; have := sum_sublist_le h; omega
  | _, _, .cons₂ a h => by rw [List.sum_cons, List.sum_cons]; have := sum_sublist_le h; omega

theorem sum_map_le {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := sum_map_le (l := l) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem countP_range_le (x : Nat) : ∀ n, (List.range n).countP (fun t => decide (t + 1 ≤ x)) ≤ x
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append]
    have ih := countP_range_le x n
    have hl : (List.range n).countP (fun t => decide (t + 1 ≤ x)) ≤ n := by
      have := List.countP_le_length (p := fun t => decide (t + 1 ≤ x)) (l := List.range n)
      rwa [List.length_range] at this
    by_cases hx : n + 1 ≤ x
    · simp [hx]; omega
    · simp [hx]; omega

theorem shareSum_cons (c : Centre) (cens : List Centre) :
    shareSum Mr S (c :: cens) = shareLocal Mr S c.v + shareSum Mr S cens := by
  simp [shareSum]

theorem shareLocal_fl (x : Nat) :
    shareLocal Mr S x = ((List.range 9).map fun k => fl Mr S (x ^^^ (1 <<< k))).sum := rfl

theorem capL_le : ∀ (cens : List Centre) (spec : List (List (Nat × Nat))),
    (∀ s ∈ spec, subl (s.map (·.1)) (List.range 9) = true) →
    (capL cens spec).countP (fun p => decide (p.2 ≤ fl Mr S p.1)) ≤ shareSum Mr S cens
  | [], _, _ => by simp [capL]
  | _ :: _, [], _ => by simp [capL]
  | c :: cens, s :: spec, hs => by
    simp only [capL]
    rw [List.countP_append, shareSum_cons]
    have ih := capL_le cens spec (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
    have h1 : (s.flatMap fun kt => (List.range kt.2).map fun t => (c.v ^^^ (1 <<< kt.1), t + 1)).countP
        (fun p => decide (p.2 ≤ fl Mr S p.1)) ≤
        ((s.map (·.1)).map fun k => fl Mr S (c.v ^^^ (1 <<< k))).sum := by
      rw [List.countP_flatMap, List.map_map]
      apply sum_map_le
      intro kt _
      simp only [Function.comp, List.countP_map]
      exact countP_range_le (fl Mr S (c.v ^^^ 1 <<< kt.1)) kt.2
    have h2 := sum_sublist_le ((subl_sublist (hs s List.mem_cons_self)).map
      (fun k => fl Mr S (c.v ^^^ (1 <<< k))))
    rw [shareLocal_fl]
    omega

theorem cap_total {w : List Nat} {cens : List Centre} {t : Tot}
    (h : totOK M X w cens t = true) (hk : isCap t.kind = true) :
    t.lits.countP (lv (baseS S E M X Mr)) ≤ shareSum Mr S cens := by
  unfold totOK at h
  cases hk' : t.kind with
  | emp q => rw [hk'] at hk; simp [isCap] at hk
  | nb q => rw [hk'] at hk; simp [isCap] at hk
  | cap spec =>
    rw [hk'] at h
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨_, hu, hm, hs⟩ := h
    have : t.lits.countP (lv (baseS S E M X Mr)) =
        (t.lits.map (uQT X)).countP (fun p => decide (p.2 ≤ fl Mr S p.1)) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro a ha
      rw [base_posU (hu a ha)]; rfl
    rw [this, (List.isPerm_iff.mp hm).countP_eq]
    exact capL_le cens spec hs

theorem bc_total (i lo hi : Nat) :
    bc S E M X Mr tots i lo hi ≤ (tots.getD i dfltTot).lits.countP (lv (baseS S E M X Mr)) :=
  countP_blk_total _ _ _ _

theorem old_clause {cl : List Nat} (ho : oldLits M cl = true)
    (h : clauseTrue (tau S E M cs) (cl.map decodeLit) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  unfold clauseTrue at h ⊢
  rw [List.any_map, List.any_eq_true] at h ⊢
  obtain ⟨a, ha, hv⟩ := h
  refine ⟨a, ha, ?_⟩
  simp only [oldLits, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ho
  obtain ⟨h2, hv2⟩ := ho a ha
  simp only [Function.comp] at hv ⊢
  rw [decode_eq _ h2] at hv ⊢
  rwa [lv_congr (τ₂ := tau S E M cs) (tauS_old hv2)]



end Snake9.LocalWindow.Tags185

#print axioms Snake9.LocalWindow.Tags185.cap_total
