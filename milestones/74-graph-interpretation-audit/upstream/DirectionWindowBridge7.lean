/-
The window premises of a seven-centre automaton from its window certificates, for an
arbitrary table bundle `T : Tables7` and key lists.

Core Lean only.  Extends `DirectionWindowBridge6`:

* k6 and F8 keys (`keys`): windows of 3..8 directions, fully counted.  `Cover7 T keys` is
  the k6 cover for lengths 3..8 (`rowOK6` on `T.k6`).  For large key sets it is checked row
  by row against one chunk of the key list each (`cover7_rows`, `rowOK6_mono`), so a row
  declaration reads a few hundred keys instead of all of them.
* H9 keys (`hkeys`): 9 directions and 7 counts, stored reversed (uncounted vertex last), so
  that the certificate is `Refuted (winOf ds) (boundsOf syms)` with 7 bounds.  The table is
  the search tree `T.htree`; `CoverH T hkeys` says that its in-order list is the list of the
  base-9 codes of the keys (one cheap kernel evaluation), and `encB_inj` decodes a hit.
* `refuted_dirH` (new): a certificate with 7 bounds on a 9-direction window excludes its
  counts on the first seven interior vertices of a snake window; the eighth interior vertex
  is unconstrained (`refuted_extend` adds the trivial bound `(0, 21)`).
* `no_forb_H9`: no H9 window of a snake is excluded, by reversal (`revSnake`).
* `direction_windows_core7`: the premises `Windows7` of `total_bound7`.

The closed-set skip of `check7At` needs no premise of its own: `step7_raw` discharges it
from the k6 windows of the source state, which are part of `Windows7` (`Windows6`).
-/
import WindowAutomaton7Defs
import DirectionWindowBridge6

namespace Snake9.DirectionWindow7
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
  Snake9.DirectionWindow6

set_option maxHeartbeats 1000000

/-! ## The k6 and F8 cover (windows of 3 to 8 directions) -/

/-- Every exclusion row of a canonical shape of 3 to 8 directions is covered by the keys. -/
def Cover7 (T : Tables7) (keys : List (List Nat × List Nat)) : Prop :=
  ∀ c, isRGS c 0 = true → 3 ≤ c.length → c.length ≤ 8 → ∀ s0, s0 < 7 →
    rowOK6 T.k6 keys c s0 = true

theorem cover6_of_cover7 {T : Tables7} {keys : List (List Nat × List Nat)} (hc : Cover7 T keys) :
    Cover6 T.k6 keys :=
  fun c hr h1 h2 s0 hs => hc c hr h1 (by omega) s0 hs

theorem keyMask6_of_mem (c : List Nat) (s0 : Nat) (rest : List Nat) :
    ∀ (keys : List (List Nat × List Nat)), (c, s0 :: rest) ∈ keys →
      (keyMask6 c s0 keys).testBit (symIdx rest 0) = true
  | [], h => absurd h List.not_mem_nil
  | k :: ks, h => by
    unfold keyMask6
    rw [Nat.testBit_or]
    rcases List.mem_cons.1 h with h | h
    · subst h
      simp [keyBit6, Nat.testBit_two_pow_self]
    · rw [keyMask6_of_mem c s0 rest ks h, Bool.or_true]

/-- A row covered by a sub-list of the keys is covered by the keys. -/
theorem rowOK6_mono (T : Tables6) {sub keys : List (List Nat × List Nat)}
    (hs : ∀ k ∈ sub, k ∈ keys) {c : List Nat} {s0 : Nat} (h : rowOK6 T sub c s0 = true) :
    rowOK6 T keys c s0 = true := by
  unfold rowOK6 at h ⊢
  generalize T.forb (T.wIdx (shapeCode c)) s0 = M at h ⊢
  rcases Bool.or_eq_true_iff.1 h with h0 | hsub
  · rw [h0]
    rfl
  · refine Bool.or_eq_true_iff.2 (Or.inr ?_)
    have hsub' : M &&& keyMask6 c s0 sub = M := by simpa using hsub
    simp only [beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hM : M.testBit i
    · rfl
    · have hk : (keyMask6 c s0 sub).testBit i = true := by
        rw [← hsub', Nat.testBit_and] at hM
        exact (Bool.and_eq_true_iff.1 hM).2
      obtain ⟨rest, hmem, hidx⟩ := keyMask6_spec c s0 sub i hk
      rw [← hidx, keyMask6_of_mem c s0 rest keys (hs _ hmem)]
      rfl

theorem mem_flatten_getD {chunks : List (List (List Nat × List Nat))} {i : Nat}
    {k : List Nat × List Nat} (h : k ∈ chunks.getD i []) : k ∈ chunks.flatten := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hc : chunks[i]? with
  | none => rw [hc] at h; exact absurd h List.not_mem_nil
  | some L =>
    rw [hc] at h
    exact List.mem_flatten.2 ⟨L, List.mem_of_getElem? hc, h⟩

/-- `Cover7` for large key sets given in chunks: one kernel evaluation per window length
shows that only the listed rows are nonzero, and each listed row is checked against one
chunk in a declaration of its own. -/
theorem cover7_rows {T : Tables7} (chunks : List (List (List Nat × List Nat)))
    (rows : List (List Nat × Nat))
    (h3 : allRGS 3 0 (zeroOutside6 T.k6 rows) = true) (h4 : allRGS 4 0 (zeroOutside6 T.k6 rows) = true)
    (h5 : allRGS 5 0 (zeroOutside6 T.k6 rows) = true) (h6 : allRGS 6 0 (zeroOutside6 T.k6 rows) = true)
    (h7 : allRGS 7 0 (zeroOutside6 T.k6 rows) = true) (h8 : allRGS 8 0 (zeroOutside6 T.k6 rows) = true)
    (hr : ∀ r ∈ rows, ∃ i, rowOK6 T.k6 (chunks.getD i []) r.1 r.2 = true) :
    Cover7 T chunks.flatten := by
  intro c hc hn1 hn2 s0 hs0
  have hz : zeroOutside6 T.k6 rows c = true := by
    have : c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨ c.length = 6 ∨ c.length = 7 ∨
      c.length = 8 := by omega
    rcases this with e | e | e | e | e | e
    · exact allRGS_spec 3 0 _ h3 c e hc
    · exact allRGS_spec 4 0 _ h4 c e hc
    · exact allRGS_spec 5 0 _ h5 c e hc
    · exact allRGS_spec 6 0 _ h6 c e hc
    · exact allRGS_spec 7 0 _ h7 c e hc
    · exact allRGS_spec 8 0 _ h8 c e hc
  have h := allBelow_spec 7 _ hz s0 hs0
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · unfold rowOK6
    rw [h0]
    rfl
  · obtain ⟨i, hi⟩ := hr (c, s0) (of_decide_eq_true hm)
    exact rowOK6_mono T.k6 (fun k hk => mem_flatten_getD hk) hi

/-- `Cover7` for small key sets: one kernel evaluation. -/
def cover7 (T : Tables7) (keys : List (List Nat × List Nat)) : Bool :=
  cover6 T.k6 keys && allRGS 8 0 (coverRow6 T.k6 keys)

theorem cover7_ok {T : Tables7} {keys : List (List Nat × List Nat)} (hc : cover7 T keys = true) :
    Cover7 T keys := by
  intro c hr hn1 hn2 s0 hs0
  simp only [cover7, Bool.and_eq_true] at hc
  by_cases h8 : c.length = 8
  · exact allBelow_spec 7 _ (allRGS_spec 8 0 _ hc.2 c h8 hr) s0 hs0
  · exact cover6_ok hc.1 c hr hn1 (by omega) s0 hs0

theorem cover7_spec {T : Tables7} {keys : List (List Nat × List Nat)} (hc : Cover7 T keys)
    (hv : keysOK6 keys = true) {c syms : List Nat} (hr : isRGS c 0 = true)
    (hn : 3 ≤ c.length ∧ c.length ≤ 8) (hl : syms.length + 1 = c.length) (hs : ∀ s ∈ syms, s ≤ 6)
    (hb : forbBit6 T.k6 (shapeCode c) syms = true) : (c, syms) ∈ keys := by
  cases syms with
  | nil => simp [forbBit6] at hb
  | cons s0 rest =>
    have hs0 : s0 ≤ 6 := hs s0 List.mem_cons_self
    have hrow0 := hc c hr hn.1 hn.2 s0 (by omega)
    unfold rowOK6 at hrow0
    have hbit := testBit_of_forbBit hb
    generalize T.k6.forb (T.k6.wIdx (shapeCode c)) s0 = M at hrow0 hbit
    rcases Bool.or_eq_true_iff.1 hrow0 with h0 | hsub
    · rw [show M = 0 by simpa using h0, Nat.zero_testBit] at hbit
      exact absurd hbit (by decide)
    · have hsub' : M &&& keyMask6 c s0 keys = M := by simpa using hsub
      have hk : (keyMask6 c s0 keys).testBit (symIdx rest 0) = true := by
        rw [← hsub', Nat.testBit_and] at hbit
        exact (Bool.and_eq_true_iff.1 hbit).2
      obtain ⟨rest', hmem, hidx⟩ := keyMask6_spec c s0 keys _ hk
      have hkv := List.all_eq_true.1 hv _ hmem
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
        List.length_cons] at hkv
      have : rest' = rest := symIdx_inj rest' rest (by simp at hl; omega)
        (fun s h => hkv.2 s (List.mem_cons_of_mem _ h))
        (fun s h => by have := hs s (List.mem_cons_of_mem _ h); omega) hidx
      rw [← this]
      exact hmem

/-! ## The H9 table -/

/-- Shape of the H9 keys: 9 directions and 7 counts, all digits below 9. -/
def keysOKH (hkeys : List (List Nat × List Nat)) : Bool :=
  hkeys.all (fun k => k.1.length == 9 && k.2.length == 7 && k.1.all (· < 9) && k.2.all (· < 9))

/-- The H9 tree holds exactly the codes of the H9 keys (in order). -/
def CoverH (T : Tables7) (hkeys : List (List Nat × List Nat)) : Prop :=
  T.htree.toList = hkeys.map (fun k => encB 9 (k.1 ++ k.2) 0)

/-- `CoverH` as one Boolean kernel evaluation. -/
def coverHb (T : Tables7) (hkeys : List (List Nat × List Nat)) : Bool :=
  T.htree.toList == hkeys.map (fun k => encB 9 (k.1 ++ k.2) 0)

theorem coverH_of {T : Tables7} {hkeys : List (List Nat × List Nat)} (h : coverHb T hkeys = true) :
    CoverH T hkeys := by
  simpa [coverHb] using h

/-- `CoverH` chunk by chunk, for a spine table (one kernel evaluation per chunk). -/
theorem coverH_spine {T : Tables7} (ps : List (NTree × Nat))
    (chunks : List (List (List Nat × List Nat))) (ht : T.htree = NTree.spine ps)
    (hl : ps.length = chunks.length)
    (hc : ∀ i, i < ps.length → (ps.getD i (.nil, 0)).1.toList ++ [(ps.getD i (.nil, 0)).2] =
      (chunks.getD i []).map (fun k => encB 9 (k.1 ++ k.2) 0)) :
    CoverH T chunks.flatten := by
  unfold CoverH
  rw [ht, NTree.spine_toList, List.map_flatten]
  congr 1
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.length_map] at h1
    have := hc i h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem (show i < chunks.length by omega), Option.getD_some] at this
    simp only [List.getElem_map]
    exact this

theorem keysOK6_flatten {chunks : List (List (List Nat × List Nat))}
    (h : ∀ i, i < chunks.length → keysOK6 (chunks.getD i []) = true) :
    keysOK6 chunks.flatten = true := by
  unfold keysOK6 at h ⊢
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨L, hL, hkL⟩ := List.mem_flatten.1 hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.all_eq_true] at this
  exact this k hkL

theorem keysOKH_flatten {chunks : List (List (List Nat × List Nat))}
    (h : ∀ i, i < chunks.length → keysOKH (chunks.getD i []) = true) :
    keysOKH chunks.flatten = true := by
  unfold keysOKH at h ⊢
  rw [List.all_eq_true]
  intro k hk
  obtain ⟨L, hL, hkL⟩ := List.mem_flatten.1 hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.all_eq_true] at this
  exact this k hkL

theorem encB_acc (b : Nat) : ∀ (l : List Nat) (acc : Nat), encB b l acc = acc * b ^ l.length + encB b l 0
  | [], acc => by simp [encB]
  | a :: l, acc => by
    show encB b l (acc * b + a) = acc * b ^ (l.length + 1) + encB b l (0 * b + a)
    rw [encB_acc b l (acc * b + a), encB_acc b l (0 * b + a), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    rw [Nat.mul_assoc, Nat.mul_comm b (b ^ l.length)]
    omega

theorem encB_cons (b a : Nat) (l : List Nat) : encB b (a :: l) 0 = a * b ^ l.length + encB b l 0 := by
  show encB b l (0 * b + a) = _
  rw [encB_acc]
  simp

theorem encB_lt (b : Nat) : ∀ (l : List Nat), (∀ s ∈ l, s < b) → encB b l 0 < b ^ l.length
  | [], _ => by simp [encB]
  | a :: l, h => by
    rw [encB_cons]
    have ha : a < b := h a List.mem_cons_self
    have hl := encB_lt b l (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have h7 : (a + 1) * b ^ l.length ≤ b * b ^ l.length := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h7
    show a * b ^ l.length + encB b l 0 < b ^ (l.length + 1)
    rw [Nat.pow_succ, Nat.mul_comm (b ^ l.length) b]
    omega

theorem encB_inj (b : Nat) : ∀ (l l' : List Nat), l.length = l'.length → (∀ s ∈ l, s < b) →
    (∀ s ∈ l', s < b) → encB b l 0 = encB b l' 0 → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: l, c :: l', hlen, ha, hb, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [encB_cons, encB_cons, ← hlen] at he
    have hl := encB_lt b l (fun s hs => ha s (List.mem_cons_of_mem _ hs))
    have hl' := encB_lt b l' (fun s hs => hb s (List.mem_cons_of_mem _ hs))
    rw [← hlen] at hl'
    have hP : 0 < b ^ l.length := Nat.pow_pos (by
      have := ha a List.mem_cons_self
      omega)
    have e1 : (encB b l 0 + a * b ^ l.length) / b ^ l.length = a := by
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hl, Nat.zero_add]
    have e2 : (encB b l' 0 + c * b ^ l.length) / b ^ l.length = c := by
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hl', Nat.zero_add]
    have hac : a = c := by
      rw [← e1, ← e2, Nat.add_comm (encB b l 0), Nat.add_comm (encB b l' 0), he]
    subst hac
    have hrest : encB b l 0 = encB b l' 0 := by omega
    rw [encB_inj b l l' hlen (fun s hs => ha s (List.mem_cons_of_mem _ hs))
      (fun s hs => hb s (List.mem_cons_of_mem _ hs)) hrest]

theorem isRGS_lt : ∀ (l : List Nat) (m : Nat), isRGS l m = true → ∀ x ∈ l, x < m + l.length
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | a :: l, m, h, x, hx => by
    simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := isRGS_lt l _ h.2
    simp only [List.length_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := ih x hx
      split at this <;> omega

/-- A hit of the H9 tree is an H9 key. -/
theorem coverH_spec {T : Tables7} {hkeys : List (List Nat × List Nat)} (hc : CoverH T hkeys)
    (hv : keysOKH hkeys = true) {ds syms : List Nat} (hl : ds.length = 9) (hsl : syms.length = 7)
    (hs : ∀ s ∈ syms, s ≤ 6) (hb : wforbH T ds syms = true) :
    (canon ds.reverse, syms.reverse) ∈ hkeys := by
  unfold wforbH at hb
  have hm := NTree.mem_toList _ _ hb
  rw [hc, List.mem_map] at hm
  obtain ⟨k, hk, he⟩ := hm
  have hkv := List.all_eq_true.1 hv _ hk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hkv
  obtain ⟨⟨⟨hk1, hk2⟩, hk3⟩, hk4⟩ := hkv
  have hcl : (canon ds.reverse).length = 9 := by rw [length_canon, List.length_reverse, hl]
  have hcd : ∀ x ∈ canon ds.reverse, x < 9 := by
    intro x hx
    have := isRGS_lt _ 0 (canon_isRGS _) x hx
    omega
  have hs' : ∀ s ∈ syms.reverse, s ≤ 6 := fun s h => hs s (List.mem_reverse.1 h)
  have heq := encB_inj 9 _ _ (by simp [hk1, hk2, hcl, hsl]) (by
      intro s hs
      rcases List.mem_append.1 hs with h | h
      · exact hk3 s h
      · exact hk4 s h) (by
      intro s hs
      rcases List.mem_append.1 hs with h | h
      · exact hcd s h
      · have := hs' s h
        omega) he
  obtain ⟨h1, h2⟩ := List.append_inj heq (by rw [hk1, hcl])
  rw [← h1, ← h2]
  exact hk

/-! ## Certificates with one interior vertex uncounted -/

theorem getD_append_left {α : Type} (l l' : List α) (d : α) {i : Nat} (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_length {α : Type} (l l' : List α) (d : α) :
    (l ++ l').getD l.length d = l'.getD 0 d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]

/-- Adding a trivial count bound keeps a refutation (the extra centre only adds a
hypothesis that every snake satisfies). -/
theorem refuted_extend {W : List Nat} {bounds : List (Nat × Nat)} (b : Nat × Nat)
    (h : Refuted W bounds) : Refuted W (bounds ++ [b]) := by
  intro S E hax
  apply h S E
  refine { hax with alpha := ?_ }
  intro c hc
  apply hax.alpha c
  simp only [centresOf, List.mem_map, List.mem_range, List.length_append, List.length_singleton] at hc ⊢
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨i, by omega, ?_⟩
  rw [getD_append_left _ _ _ hi]

/-- A direction certificate with `cs.length - 2` count bounds excludes its counts on the
first `cs.length - 2` interior vertices of every snake window relabelled onto `cs`; the last
interior vertex is unconstrained. -/
theorem refuted_dirH {cs syms u : List Nat} (h : Refuted (winOf cs) (boundsOf syms))
    {m : Nat} (p : Snake m) (r : Nat) (hlen : syms.length + 2 = cs.length)
    (hr : r + cs.length ≤ m) (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < cs.length → cs.getD j 0 < u.length ∧ u.getD (cs.getD j 0) 0 = dir p (r + j))
    (hs : ∀ i, i < syms.length → syms.getD i 0 = symC (coreAlpha p (r + i + 1))) : False := by
  have hlen9 : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hsp := mkPerm_spec hu hu9 hlen9
  have h' := refuted_extend (0, 21) h
  refine refuted_bridge p (mkPerm u) r h' (canon_winOf cs)
    (by simp [boundsOf]; omega) hr ?_ ?_
  · intro j hj
    obtain ⟨h1, h2⟩ := hcs j hj
    rw [← h2]
    exact hsp _ h1
  · intro i hi
    simp only [List.length_append, boundsOf, List.length_map, List.length_singleton] at hi
    by_cases hi' : i < syms.length
    · rw [getD_append_left _ _ _ (by simpa [boundsOf] using hi'), getD_boundsOf hi', hs i hi']
      exact boundOf_symC (coreAlpha_le_21 p (by omega) (by omega))
    · have he : i = (boundsOf syms).length := by simp [boundsOf]; omega
      rw [he, getD_append_length]
      exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by rw [show (boundsOf syms).length = syms.length by simp [boundsOf]]; omega)⟩

/-! ## Windows of a snake -/

section Window
variable {m : Nat} (p : Snake m)

theorem window_refute7 {T : Tables7} {keys : List (List Nat × List Nat)} (h : AllRefutedList keys)
    (hv : keysOK6 keys = true) (hc : Cover7 T keys) (r n : Nat) (hn : 3 ≤ n ∧ n ≤ 8)
    (hr : r + n ≤ m) (hb : wforbA6 T.k6 (dsOf p r n) (symsOf p r n) = true) : False := by
  have hlen := length_dsOf p r n
  have hslen := length_symsOf p r n
  have hkey : (canon (dsOf p r n), symsOf p r n) ∈ keys := by
    refine cover7_spec hc hv (canon_isRGS _) (by rw [length_canon]; omega)
      (by rw [length_canon]; omega) ?_ hb
    intro s hs
    simp only [symsOf, List.mem_map] at hs
    obtain ⟨i, _, rfl⟩ := hs
    exact symC_le_six _
  have href : Refuted (winOf (canon (dsOf p r n))) (boundsOf (symsOf p r n)) :=
    AllRefutedList.mem h _ hkey
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ seenAfter [] (dsOf p r n) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_dir href p r (u := seenAfter [] (dsOf p r n)) (by rw [length_canon]; omega)
    (by rw [length_canon]; omega) (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r n)).getD j 0 = idx (seenAfter [] (dsOf p r n)) ((dsOf p r n).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    exact getD_symsOf p (by omega)

/-- No window of three to eight directions is excluded by `wforb6 T.k6`, in either
orientation. -/
theorem no_forb_window7 {T : Tables7} {keys : List (List Nat × List Nat)} (h : AllRefutedList keys)
    (hv : keysOK6 keys = true) (hc : Cover7 T keys) (r n : Nat) (hn : 3 ≤ n ∧ n ≤ 8)
    (hr : r + n ≤ m) : wforb6 T.k6 (dsOf p r n) (symsOf p r n) = false := by
  cases hw : wforb6 T.k6 (dsOf p r n) (symsOf p r n)
  · rfl
  · exfalso
    unfold wforb6 at hw
    rcases Bool.or_eq_true_iff.1 hw with h1 | h1
    · exact window_refute7 p h hv hc r n hn hr h1
    · rw [← dsOf_rev p r n hr, ← symsOf_rev p r n hr] at h1
      exact window_refute7 (revSnake p) h hv hc (m - r - n) n hn (by omega) h1

/-- An H9 key on the window of 9 directions at `r`, counted on its first seven interior
vertices, contradicts its certificate. -/
theorem window_refuteH {hkeys : List (List Nat × List Nat)} (h : AllRefutedList hkeys)
    (r : Nat) (hr : r + 9 ≤ m)
    (hkey : (canon (dsOf p r 9), (symsOf p r 9).take 7) ∈ hkeys) : False := by
  have hlen := length_dsOf p r 9
  have href := AllRefutedList.mem h _ hkey
  have hmem : ∀ j, j < 9 → (dsOf p r 9).getD j 0 ∈ seenAfter [] (dsOf p r 9) := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_dirH href p r (u := seenAfter [] (dsOf p r 9))
    (by simp only [List.length_take, length_canon, length_symsOf, hlen]; omega)
    (by rw [length_canon]; omega)
    (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro j hj
    rw [length_canon] at hj
    have e : (canon (dsOf p r 9)).getD j 0 = idx (seenAfter [] (dsOf p r 9)) ((dsOf p r 9).getD j 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem j (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem j (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    have hi7 : i < 7 := by simpa [length_symsOf] using hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi7, ← List.getD_eq_getElem?_getD]
    exact getD_symsOf p (by omega)

theorem reverse_drop_one (l : List Nat) : (l.drop 1).reverse = l.reverse.take (l.length - 1) := by
  apply List.ext_getElem
  · simp only [List.length_reverse, List.length_drop, List.length_take]; omega
  · intro i h1 h2
    simp only [List.length_reverse, List.length_drop] at h1
    simp only [List.getElem_reverse, List.getElem_drop, List.getElem_take, List.length_drop]
    congr 1
    omega

/-- No H9 window of a snake is excluded: directions `d(r..r+8)`, counts of the interior
vertices `r+2..r+8` (the vertex `r+1` uncounted). -/
theorem no_forb_H9 {T : Tables7} {hkeys : List (List Nat × List Nat)} (h : AllRefutedList hkeys)
    (hv : keysOKH hkeys = true) (hc : CoverH T hkeys) (r : Nat) (hr : r + 9 ≤ m) :
    wforbH T (dsOf p r 9) ((symsOf p r 9).drop 1) = false := by
  cases hw : wforbH T (dsOf p r 9) ((symsOf p r 9).drop 1)
  · rfl
  · exfalso
    have hkey := coverH_spec hc hv (length_dsOf p r 9) (by simp [length_symsOf]) (by
      intro s hs
      have hs' := List.mem_of_mem_drop hs
      simp only [symsOf, List.mem_map] at hs'
      obtain ⟨i, _, rfl⟩ := hs'
      exact symC_le_six _) hw
    rw [← dsOf_rev p r 9 hr, reverse_drop_one, length_symsOf, ← symsOf_rev p r 9 hr] at hkey
    exact window_refuteH (revSnake p) h (m - r - 9) (by omega) hkey

end Window

/-- The window premises of the seven-centre sequence bound (`Windows7`), for the path
directions and the core singleton count `coreAlpha`, from the certificate statements of the
k6/F8 keys and of the H9 keys. -/
theorem direction_windows_core7 {T : Tables7} {keys hkeys : List (List Nat × List Nat)}
    (h : AllRefutedList keys) (hv : keysOK6 keys = true) (hc : Cover7 T keys)
    (hh : AllRefutedList hkeys) (hvh : keysOKH hkeys = true) (hch : CoverH T hkeys)
    {m : Nat} (p : Snake m) : Windows7 T (pathDir p) (coreAlpha p) m := by
  refine ⟨direction_windows_core6 h hv (cover6_of_cover7 hc) p, fun j hj => ?_, fun j hj => ?_⟩
  · have := no_forb_window7 p h hv hc j 8 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_H9 p hh hvh hch j hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this

end Snake9.DirectionWindow7

#print axioms Snake9.DirectionWindow7.cover7_rows
#print axioms Snake9.DirectionWindow7.coverH_spec
#print axioms Snake9.DirectionWindow7.coverH_spine
#print axioms Snake9.DirectionWindow7.refuted_dirH
#print axioms Snake9.DirectionWindow7.no_forb_H9
#print axioms Snake9.DirectionWindow7.direction_windows_core7
