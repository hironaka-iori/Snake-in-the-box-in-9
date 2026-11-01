/-
The direction-aware window premises of a six-centre automaton from its window
certificates, for an arbitrary table bundle `T : Tables6` and key list.

Core Lean only.  Generalises `DirectionWindowBridge5R4` (windows of 3..6 directions,
cover by enumerating every count list of every listed shape) to windows of 3..7
directions.  Enumerating the 7^6 count lists of each 7-direction shape would cost about
17 times the five-centre cover, so the cover is checked row by row instead:

* `keyMask6 c s0 keys`: the mask of the keys with direction list `c` and first count `s0`
  (bit `symIdx` of the other counts);
* `Cover6 T keys`: for every restricted growth string `c` of length 3..7 and every first
  count `s0 ≤ 6`, the exclusion row of `c` is zero or a subset of `keyMask6 c s0 keys`
  (`rowOK6`); proved by one kernel evaluation (`cover6_ok`, small key sets) or row by row
  (`cover6_rows`: the nonzero rows are listed, each is checked in its own declaration);
* `keysOK6 keys`: every key has one count fewer than directions and counts below 7, so
  `symIdx` is injective on the counts of equal length (`symIdx_inj`).

Then `cover6_spec`: a set exclusion bit of a canonical shape is a certificate key, and
`window_refute6` / `no_forb_window6` / `direction_windows_core6` are the five-centre
arguments verbatim (`refuted_dir` realises the relabelling `canon`).
-/
import WindowAutomaton6Defs
import DirectionWindowBridge

namespace Snake9.DirectionWindow6
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

set_option maxHeartbeats 1000000

/-! ## Key masks -/

/-- The bit of one key `(ds, syms)` in the mask of direction list `c` and first count `s0`. -/
def keyBit6 (c : List Nat) (s0 : Nat) (ds : List Nat) : List Nat → Nat
  | [] => 0
  | s :: rest => if decide (ds = c) && s == s0 then 1 <<< symIdx rest 0 else 0

def keyMask6 (c : List Nat) (s0 : Nat) : List (List Nat × List Nat) → Nat
  | [] => 0
  | k :: ks => keyBit6 c s0 k.1 k.2 ||| keyMask6 c s0 ks

/-- Shape of the keys: one count fewer than directions, counts below seven. -/
def keysOK6 (keys : List (List Nat × List Nat)) : Bool :=
  keys.all (fun k => k.2.length + 1 == k.1.length && k.2.all (· < 7))

/-- The exclusion row `(c, s0)` is zero or covered by the keys. -/
def rowOK6 (T : Tables6) (keys : List (List Nat × List Nat)) (c : List Nat) (s0 : Nat) : Bool :=
  T.forb (T.wIdx (shapeCode c)) s0 == 0 ||
  (T.forb (T.wIdx (shapeCode c)) s0 &&& keyMask6 c s0 keys == T.forb (T.wIdx (shapeCode c)) s0)

/-- The exclusion rows of the canonical shape `c` are covered by the keys. -/
def coverRow6 (T : Tables6) (keys : List (List Nat × List Nat)) (c : List Nat) : Bool :=
  allBelow 7 (fun s0 => rowOK6 T keys c s0)

/-- Every canonical window shape of 3 to 7 directions is covered (one kernel evaluation;
fine for small key sets). -/
def cover6 (T : Tables6) (keys : List (List Nat × List Nat)) : Bool :=
  allRGS 3 0 (coverRow6 T keys) && allRGS 4 0 (coverRow6 T keys) &&
  allRGS 5 0 (coverRow6 T keys) && allRGS 6 0 (coverRow6 T keys) && allRGS 7 0 (coverRow6 T keys)

/-- What the bridge needs: every exclusion row of a canonical shape of 3 to 7 directions is
covered. -/
def Cover6 (T : Tables6) (keys : List (List Nat × List Nat)) : Prop :=
  ∀ c, isRGS c 0 = true → 3 ≤ c.length → c.length ≤ 7 → ∀ s0, s0 < 7 → rowOK6 T keys c s0 = true

theorem cover6_ok {T : Tables6} {keys : List (List Nat × List Nat)} (hc : cover6 T keys = true) :
    Cover6 T keys := by
  intro c hr hn1 hn2 s0 hs0
  have hrow : coverRow6 T keys c = true := by
    simp only [cover6, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩ := hc
    have : c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨ c.length = 6 ∨ c.length = 7 := by omega
    rcases this with e | e | e | e | e
    · exact allRGS_spec 3 0 _ h3 c e hr
    · exact allRGS_spec 4 0 _ h4 c e hr
    · exact allRGS_spec 5 0 _ h5 c e hr
    · exact allRGS_spec 6 0 _ h6 c e hr
    · exact allRGS_spec 7 0 _ h7 c e hr
  exact allBelow_spec 7 _ hrow s0 hs0

/-- The rows outside the list `rows` are zero. -/
def zeroOutside6 (T : Tables6) (rows : List (List Nat × Nat)) (c : List Nat) : Bool :=
  allBelow 7 (fun s0 => T.forb (T.wIdx (shapeCode c)) s0 == 0 || decide ((c, s0) ∈ rows))

/-- `Cover6` for large key sets: one cheap kernel evaluation per window length shows that
only the listed rows are nonzero, and each listed row is checked in a declaration of its
own (`rowOK6`, one pass over the keys), so the kernel caches of one row are released
before the next. -/
theorem cover6_rows {T : Tables6} {keys : List (List Nat × List Nat)} (rows : List (List Nat × Nat))
    (h3 : allRGS 3 0 (zeroOutside6 T rows) = true) (h4 : allRGS 4 0 (zeroOutside6 T rows) = true)
    (h5 : allRGS 5 0 (zeroOutside6 T rows) = true) (h6 : allRGS 6 0 (zeroOutside6 T rows) = true)
    (h7 : allRGS 7 0 (zeroOutside6 T rows) = true)
    (hr : ∀ r ∈ rows, rowOK6 T keys r.1 r.2 = true) : Cover6 T keys := by
  intro c hc hn1 hn2 s0 hs0
  have hz : zeroOutside6 T rows c = true := by
    have : c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨ c.length = 6 ∨ c.length = 7 := by omega
    rcases this with e | e | e | e | e
    · exact allRGS_spec 3 0 _ h3 c e hc
    · exact allRGS_spec 4 0 _ h4 c e hc
    · exact allRGS_spec 5 0 _ h5 c e hc
    · exact allRGS_spec 6 0 _ h6 c e hc
    · exact allRGS_spec 7 0 _ h7 c e hc
  have h := allBelow_spec 7 _ hz s0 hs0
  rcases Bool.or_eq_true_iff.1 h with h0 | hm
  · unfold rowOK6
    rw [h0]
    rfl
  · exact hr (c, s0) (of_decide_eq_true hm)

theorem testBit_keyBit6 {c ds syms : List Nat} {s0 i : Nat} (h : (keyBit6 c s0 ds syms).testBit i = true) :
    ∃ rest, ds = c ∧ syms = s0 :: rest ∧ symIdx rest 0 = i := by
  cases syms with
  | nil => simp [keyBit6] at h
  | cons s rest =>
    simp only [keyBit6] at h
    by_cases hc : decide (ds = c) && s == s0
    · rw [if_pos hc, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact ⟨rest, hc.1, by rw [hc.2], of_decide_eq_true h⟩
    · rw [if_neg hc, Nat.zero_testBit] at h
      exact absurd h (by decide)

theorem keyMask6_spec (c : List Nat) (s0 : Nat) : ∀ (keys : List (List Nat × List Nat)) (i : Nat),
    (keyMask6 c s0 keys).testBit i = true → ∃ rest, (c, s0 :: rest) ∈ keys ∧ symIdx rest 0 = i
  | [], i, h => by simp [keyMask6] at h
  | k :: ks, i, h => by
    unfold keyMask6 at h
    rw [Nat.testBit_or] at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · obtain ⟨rest, h1, h2, h3⟩ := testBit_keyBit6 h
      refine ⟨rest, ?_, h3⟩
      have : k = (c, s0 :: rest) := by
        obtain ⟨a, b⟩ := k
        simp only at h1 h2
        rw [h1, h2]
      rw [this]
      exact List.mem_cons_self
    · obtain ⟨rest, h1, h2⟩ := keyMask6_spec c s0 ks i h
      exact ⟨rest, List.mem_cons_of_mem _ h1, h2⟩

/-! ## `symIdx` is injective on count lists of one length -/

theorem symIdx_acc : ∀ (l : List Nat) (acc : Nat), symIdx l acc = acc * 7 ^ l.length + symIdx l 0
  | [], acc => by simp [symIdx]
  | a :: l, acc => by
    show symIdx l (acc * 7 + a) = acc * 7 ^ (l.length + 1) + symIdx l (0 * 7 + a)
    rw [symIdx_acc l (acc * 7 + a), symIdx_acc l (0 * 7 + a), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    rw [Nat.mul_assoc, Nat.mul_comm 7 (7 ^ l.length)]
    omega

theorem symIdx_cons (a : Nat) (l : List Nat) : symIdx (a :: l) 0 = a * 7 ^ l.length + symIdx l 0 := by
  show symIdx l (0 * 7 + a) = _
  rw [symIdx_acc]
  simp

theorem symIdx_lt : ∀ (l : List Nat), (∀ s ∈ l, s < 7) → symIdx l 0 < 7 ^ l.length
  | [], _ => by simp [symIdx]
  | a :: l, h => by
    rw [symIdx_cons]
    have ha : a < 7 := h a List.mem_cons_self
    have hl := symIdx_lt l (fun s hs => h s (List.mem_cons_of_mem _ hs))
    have h7 : (a + 1) * 7 ^ l.length ≤ 7 * 7 ^ l.length := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h7
    show a * 7 ^ l.length + symIdx l 0 < 7 ^ (l.length + 1)
    rw [Nat.pow_succ, Nat.mul_comm (7 ^ l.length) 7]
    omega

theorem symIdx_inj : ∀ (l l' : List Nat), l.length = l'.length → (∀ s ∈ l, s < 7) →
    (∀ s ∈ l', s < 7) → symIdx l 0 = symIdx l' 0 → l = l'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: l, b :: l', hlen, ha, hb, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    rw [symIdx_cons, symIdx_cons, ← hlen] at he
    have hl := symIdx_lt l (fun s hs => ha s (List.mem_cons_of_mem _ hs))
    have hl' := symIdx_lt l' (fun s hs => hb s (List.mem_cons_of_mem _ hs))
    rw [← hlen] at hl'
    have hP : 0 < 7 ^ l.length := Nat.pow_pos (by decide)
    have e1 : (symIdx l 0 + a * 7 ^ l.length) / 7 ^ l.length = a := by
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hl, Nat.zero_add]
    have e2 : (symIdx l' 0 + b * 7 ^ l.length) / 7 ^ l.length = b := by
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hl', Nat.zero_add]
    have hab : a = b := by
      rw [← e1, ← e2, Nat.add_comm (symIdx l 0), Nat.add_comm (symIdx l' 0), he]
    subst hab
    have hrest : symIdx l 0 = symIdx l' 0 := by omega
    rw [symIdx_inj l l' hlen (fun s hs => ha s (List.mem_cons_of_mem _ hs))
      (fun s hs => hb s (List.mem_cons_of_mem _ hs)) hrest]

/-! ## The cover -/

theorem testBit_of_forbBit {x i : Nat} (h : ((x >>> i) &&& 1 == 1) = true) : x.testBit i = true := by
  have h1 : (x >>> i) &&& 1 = 1 := by simpa using h
  rw [Nat.and_one_is_mod] at h1
  have := Nat.testBit_shiftRight (i := i) (j := 0) x
  rw [Nat.add_zero] at this
  rw [← this, Nat.testBit_zero, h1]
  rfl

theorem cover6_spec {T : Tables6} {keys : List (List Nat × List Nat)} (hc : Cover6 T keys)
    (hv : keysOK6 keys = true) {c syms : List Nat} (hr : isRGS c 0 = true)
    (hn : 3 ≤ c.length ∧ c.length ≤ 7) (hl : syms.length + 1 = c.length) (hs : ∀ s ∈ syms, s ≤ 6)
    (hb : forbBit6 T (shapeCode c) syms = true) : (c, syms) ∈ keys := by
  cases syms with
  | nil => simp [forbBit6] at hb
  | cons s0 rest =>
    have hs0 : s0 ≤ 6 := hs s0 List.mem_cons_self
    have hrow0 := hc c hr hn.1 hn.2 s0 (by omega)
    unfold rowOK6 at hrow0
    have hbit := testBit_of_forbBit hb
    generalize T.forb (T.wIdx (shapeCode c)) s0 = M at hrow0 hbit
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

/-! ## Windows of a snake -/

section Window
variable {m : Nat} (p : Snake m)

/-- A window whose canonical shape and lumped counts hit a set exclusion bit contradicts
the certificate of that key. -/
theorem window_refute6 {T : Tables6} {keys : List (List Nat × List Nat)} (h : AllRefutedList keys)
    (hv : keysOK6 keys = true) (hc : Cover6 T keys) (r n : Nat) (hn : 3 ≤ n ∧ n ≤ 7)
    (hr : r + n ≤ m) (hb : wforbA6 T (dsOf p r n) (symsOf p r n) = true) : False := by
  have hlen := length_dsOf p r n
  have hslen := length_symsOf p r n
  have hkey : (canon (dsOf p r n), symsOf p r n) ∈ keys := by
    refine cover6_spec hc hv (canon_isRGS _) (by rw [length_canon]; omega)
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

/-- No window of three to seven directions is excluded by `wforb6 T`, in either orientation. -/
theorem no_forb_window6 {T : Tables6} {keys : List (List Nat × List Nat)} (h : AllRefutedList keys)
    (hv : keysOK6 keys = true) (hc : Cover6 T keys) (r n : Nat) (hn : 3 ≤ n ∧ n ≤ 7)
    (hr : r + n ≤ m) : wforb6 T (dsOf p r n) (symsOf p r n) = false := by
  cases hw : wforb6 T (dsOf p r n) (symsOf p r n)
  · rfl
  · exfalso
    unfold wforb6 at hw
    rcases Bool.or_eq_true_iff.1 hw with h1 | h1
    · exact window_refute6 p h hv hc r n hn hr h1
    · rw [← dsOf_rev p r n hr, ← symsOf_rev p r n hr] at h1
      exact window_refute6 (revSnake p) h hv hc (m - r - n) n hn (by omega) h1

end Window

/-- The five window premises of the six-centre sequence bound (`Windows6`), for the path
directions and the core singleton count `coreAlpha`, from the certificate statements. -/
theorem direction_windows_core6 {T : Tables6} {keys : List (List Nat × List Nat)}
    (h : AllRefutedList keys) (hv : keysOK6 keys = true) (hc : Cover6 T keys)
    {m : Nat} (p : Snake m) : Windows6 T (pathDir p) (coreAlpha p) m := by
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := no_forb_window6 p h hv hc j 3 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window6 p h hv hc j 4 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window6 p h hv hc j 5 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window6 p h hv hc j 6 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
    exact this
  · have := no_forb_window6 p h hv hc j 7 (by omega) hj
    rw [pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega),
      pathDir_eq_dir p (by omega)]
    exact this

end Snake9.DirectionWindow6

#print axioms Snake9.DirectionWindow6.cover6_spec
#print axioms Snake9.DirectionWindow6.cover6_rows
#print axioms Snake9.DirectionWindow6.direction_windows_core6
