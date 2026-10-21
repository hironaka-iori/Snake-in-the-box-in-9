import D239Ref2
import D239LexG1
import WindowAutomatonData
/-!
# Direction-aware windows (bound 239): ranges, table lemmas, packaged refutations

* `InR lo hi a`: `lo ≤ a` and `a ≤ hi`, where `hi ≥ 21` means no upper bound (every count of a
  centre is at most 21, so the certified range `[6, 21]` covers the lumped symbol `sym a = 6`).
* `cov1 r s`: the certified range `r` covers the lumped symbol `s` (`s = 6` needs `[lo ≤ 6, 21]`).
* `tab2/3/4 c L`: kernel-decidable statement "every symbol tuple (entries `0..6`) whose window
  `c` is flagged in the automaton table `forbMask` (`wforb1`) is covered by a range tuple of
  `L`"; `tab*_spec` turn it into range facts `InR` for the actual counts.
* `Refuted2` (two centres, window `0,1,3,7`) next to `WinG1.Refuted3/4`; `P2/P3/P4` read a
  range tuple as such a refutation.
* `duoF/duoB`, `triF/triB`, `quadF/quadB`: a snake through a normalised window (forwards, or
  backwards) whose counts satisfy `InR` contradicts a packaged refutation; `*_tab` combine this
  with the table lemmas: if the window `c` with the snake's lumped counts is flagged, `False`.
-/
namespace D239
open Snake9 Snake9.SquareIncidence WinCNF W223G1 WinG1 Snake9.WindowAutomaton

/-! ### Ranges and symbols -/

def InR (lo hi a : Nat) : Prop := lo ≤ a ∧ (a ≤ hi ∨ 21 ≤ hi)

def cov1 (r : Nat × Nat) (s : Nat) : Bool :=
  if s = 6 then decide (r.1 ≤ 6) && decide (21 ≤ r.2) else decide (r.1 ≤ s) && decide (s ≤ r.2)

theorem cov1_sym {lo hi a : Nat} (h : cov1 (lo, hi) (sym a) = true) : InR lo hi a := by
  unfold cov1 at h; unfold InR
  by_cases ha : a ≤ 5
  · have hs : sym a = a := by unfold sym; split <;> omega
    rw [hs] at h
    simp only [show a ≠ 6 by omega, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · have hs : sym a = 6 := by unfold sym; split <;> omega
    rw [hs] at h
    simp only [if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    omega

def covL : List (Nat × Nat) → List Nat → Bool
  | [], ss => ss.isEmpty
  | r :: rs, ss => match ss with
    | [] => false
    | s :: ss => cov1 r s && covL rs ss

def allS (p : Nat → Bool) : Bool := allBelow 7 p

theorem allS_spec {p : Nat → Bool} (h : allS p = true) (s : Nat) (hs : s ≤ 6) : p s = true :=
  allBelow_spec 7 p h s (by omega)

def tab2 (c : List Nat) (L : List (List (Nat × Nat))) : Bool :=
  allS fun s1 => allS fun s2 => !wforb1 c [s1, s2] || L.any (fun rs => covL rs [s1, s2])

def tab3 (c : List Nat) (L : List (List (Nat × Nat))) : Bool :=
  allS fun s1 => allS fun s2 => allS fun s3 =>
    !wforb1 c [s1, s2, s3] || L.any (fun rs => covL rs [s1, s2, s3])

def tab4 (c : List Nat) (L : List (List (Nat × Nat))) : Bool :=
  allS fun s1 => allS fun s2 => allS fun s3 => allS fun s4 =>
    !wforb1 c [s1, s2, s3, s4] || L.any (fun rs => covL rs [s1, s2, s3, s4])

theorem tab2_spec {c : List Nat} {L : List (List (Nat × Nat))} (ht : tab2 c L = true)
    {a1 a2 : Nat} (hw : wforb1 c [sym a1, sym a2] = true) :
    ∃ lo1 hi1 lo2 hi2, [(lo1, hi1), (lo2, hi2)] ∈ L ∧ InR lo1 hi1 a1 ∧ InR lo2 hi2 a2 := by
  have h := allS_spec (allS_spec ht _ (sym_le_six a1)) _ (sym_le_six a2)
  simp only [hw, Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨rs, hm, hc⟩ := h
  rcases rs with _ | ⟨⟨lo1, hi1⟩, _ | ⟨⟨lo2, hi2⟩, _ | ⟨_, _⟩⟩⟩ <;> simp only [covL, Bool.and_eq_true, List.isEmpty_cons, List.isEmpty_nil, Bool.and_false, Bool.false_eq_true, and_false, false_and, and_true] at hc
  exact ⟨lo1, hi1, lo2, hi2, hm, cov1_sym hc.1, cov1_sym hc.2⟩

theorem tab3_spec {c : List Nat} {L : List (List (Nat × Nat))} (ht : tab3 c L = true)
    {a1 a2 a3 : Nat} (hw : wforb1 c [sym a1, sym a2, sym a3] = true) :
    ∃ lo1 hi1 lo2 hi2 lo3 hi3, [(lo1, hi1), (lo2, hi2), (lo3, hi3)] ∈ L ∧
      InR lo1 hi1 a1 ∧ InR lo2 hi2 a2 ∧ InR lo3 hi3 a3 := by
  have h := allS_spec (allS_spec (allS_spec ht _ (sym_le_six a1)) _ (sym_le_six a2)) _
    (sym_le_six a3)
  simp only [hw, Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨rs, hm, hc⟩ := h
  rcases rs with _ | ⟨⟨lo1, hi1⟩, _ | ⟨⟨lo2, hi2⟩, _ | ⟨⟨lo3, hi3⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp only [covL, Bool.and_eq_true, List.isEmpty_cons, List.isEmpty_nil, Bool.and_false, Bool.false_eq_true, and_false, false_and, and_true] at hc
  exact ⟨lo1, hi1, lo2, hi2, lo3, hi3, hm, cov1_sym hc.1, cov1_sym hc.2.1, cov1_sym hc.2.2⟩

theorem tab4_spec {c : List Nat} {L : List (List (Nat × Nat))} (ht : tab4 c L = true)
    {a1 a2 a3 a4 : Nat} (hw : wforb1 c [sym a1, sym a2, sym a3, sym a4] = true) :
    ∃ lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4,
      [(lo1, hi1), (lo2, hi2), (lo3, hi3), (lo4, hi4)] ∈ L ∧
      InR lo1 hi1 a1 ∧ InR lo2 hi2 a2 ∧ InR lo3 hi3 a3 ∧ InR lo4 hi4 a4 := by
  have h := allS_spec (allS_spec (allS_spec (allS_spec ht _ (sym_le_six a1)) _ (sym_le_six a2))
    _ (sym_le_six a3)) _ (sym_le_six a4)
  simp only [hw, Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨rs, hm, hc⟩ := h
  rcases rs with _ | ⟨⟨lo1, hi1⟩, _ | ⟨⟨lo2, hi2⟩, _ | ⟨⟨lo3, hi3⟩, _ | ⟨⟨lo4, hi4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp only [covL, Bool.and_eq_true, List.isEmpty_cons, List.isEmpty_nil, Bool.and_false, Bool.false_eq_true, and_false, false_and, and_true] at hc
  exact ⟨lo1, hi1, lo2, hi2, lo3, hi3, lo4, hi4, hm, cov1_sym hc.1, cov1_sym hc.2.1,
      cov1_sym hc.2.2.1, cov1_sym hc.2.2.2⟩

/-! ### Packaged refutations -/

/-- Centre specifications of the normalised windows. -/
def sp2 (lo1 hi1 lo2 hi2 : Nat) : List Spec :=
  [(cornerVerts 1 0 1, lo1, hi1), (cornerVerts 3 1 2, lo2, hi2)]
def sp3 (u3 : Coord) (lo1 hi1 lo2 hi2 lo3 hi3 : Nat) : List Spec :=
  sp2 lo1 hi1 lo2 hi2 ++ [(cornerVerts 7 2 u3, lo3, hi3)]
def sp4 (u3 u4 : Coord) (lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat) : List Spec :=
  sp3 u3 lo1 hi1 lo2 hi2 lo3 hi3 ++ [(cornerVerts (flip u3 7).val u3 u4, lo4, hi4)]

/-- A refutation of the window, plain or symmetry-broken. -/
def Q2 (lo1 hi1 lo2 hi2 : Nat) : Prop :=
  Refuted2 lo1 hi1 lo2 hi2 ∨ RefutedL [0, 1, 3, 7] (sp2 lo1 hi1 lo2 hi2) [0, 1, 2]
def Q3 (u3 : Coord) (lo1 hi1 lo2 hi2 lo3 hi3 : Nat) : Prop :=
  Refuted3 u3 lo1 hi1 lo2 hi2 lo3 hi3 ∨
    RefutedL [0, 1, 3, 7, (flip u3 7).val] (sp3 u3 lo1 hi1 lo2 hi2 lo3 hi3) [0, 1, 2, u3]
def Q4 (u3 u4 : Coord) (lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat) : Prop :=
  Refuted4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 ∨
    RefutedL [0, 1, 3, 7, (flip u3 7).val, (flip u4 (flip u3 7)).val]
      (sp4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4) [0, 1, 2, u3, u4]

def P2 : List (Nat × Nat) → Prop
  | [(lo1, hi1), (lo2, hi2)] => Q2 lo1 hi1 lo2 hi2
  | _ => True

def P3 (u3 : Coord) : List (Nat × Nat) → Prop
  | [(lo1, hi1), (lo2, hi2), (lo3, hi3)] => Q3 u3 lo1 hi1 lo2 hi2 lo3 hi3
  | _ => True

def P4 (u3 u4 : Coord) : List (Nat × Nat) → Prop
  | [(lo1, hi1), (lo2, hi2), (lo3, hi3), (lo4, hi4)] => Q4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4
  | _ => True

theorem forall_nil {P : List (Nat × Nat) → Prop} : ∀ x ∈ ([] : List (List (Nat × Nat))), P x :=
  fun _ h => absurd h List.not_mem_nil

theorem forall_cons {P : List (Nat × Nat) → Prop} {x : List (Nat × Nat)}
    {l : List (List (Nat × Nat))} (h : P x) (t : ∀ y ∈ l, P y) : ∀ y ∈ x :: l, P y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact h
  · exact t y hy

/-! ### Vertices fixed by the free-coordinate permutations -/

theorem bitsIn_mono {W W' : List Coord} {v : Vertex} (h : BitsIn W v) (hs : ∀ c ∈ W, c ∈ W') :
    BitsIn W' v := fun c hc => hs c (h c hc)

theorem bitsIn_flip {W : List Coord} {v : Vertex} {u : Coord} (h : BitsIn W v) (hu : u ∈ W) :
    BitsIn W (flip u v) := by
  intro c hc
  unfold SquareIncidence.flip at hc
  rw [CubePerm.testBit_vxor, CubePerm.testBit_unit] at hc
  by_cases hcu : u.val = c.val
  · rw [← Fin.ext hcu]; exact hu
  · rw [decide_eq_false hcu, Bool.xor_false] at hc
    exact h c hc

theorem bits0 : BitsIn [0, 1, 2] (0 : Vertex) := by unfold BitsIn; decide
theorem bits1 : BitsIn [0, 1, 2] (1 : Vertex) := by unfold BitsIn; decide
theorem bits3 : BitsIn [0, 1, 2] (3 : Vertex) := by unfold BitsIn; decide
theorem bits7 : BitsIn [0, 1, 2] (7 : Vertex) := by unfold BitsIn; decide

/-! ### Centres with `InR` ranges -/

section
variable {m : Nat} (q : Snake m)

theorem centreI (ip : Nat) (hi : ip + 2 ≤ m) (c : Vertex) (u1 u2 : Coord)
    (hc : q.vertex ⟨ip+1, by omega⟩ = c) (hp : q.vertex ⟨ip, by omega⟩ = flip u1 c)
    (hn : q.vertex ⟨ip+2, by omega⟩ = flip u2 c) {cs : List Nat} (hcs : CornerOK c.val u1 u2 cs)
    {lo hi' : Nat} (ha : InR lo hi' (localAlpha q ⟨ip+1, by omega⟩)) :
    SpecHolds (sel q) (cs, lo, hi') := by
  obtain ⟨e1, e2, e3, e4⟩ := hcs
  have h := center_counts q ⟨ip+1, by omega⟩ ⟨ip, by omega⟩ ⟨ip+2, by omega⟩ rfl rfl c u1 u2
    hc hp hn cs e1 e2 (nodupB_nodup e3) e4 _ rfl
  have hl := List.length_filter_le (fun x => !sel q x) cs
  unfold SpecHolds
  unfold InR at ha
  simp only
  omega

theorem duoF_facts {lo1 hi1 lo2 hi2 : Nat} (r : Nat) (hr : r + 3 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+1, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩)) :
    (∀ w ∈ [0, 1, 3, 7], sel q w = true) ∧ ∀ s ∈ sp2 lo1 hi1 lo2 hi2, SpecHolds (sel q) s := by
  refine ⟨?_, ?_⟩
  · intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
  · intro s hs
    simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl
    · exact centreI q r (by omega) 1 0 1 h1 (by rw [h0]; decide) (by rw [h2]; decide) cok1 a1
    · exact centreI q (r+1) (by omega) 3 1 2 h2 (by rw [h1]; decide) (by rw [h3]; decide) cok3 a2

theorem duoB_facts {lo1 hi1 lo2 hi2 : Nat} (r : Nat) (hr : r + 3 ≤ m)
    (h0 : q.vertex ⟨r+3, by omega⟩ = 0) (h1 : q.vertex ⟨r+2, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+1, by omega⟩ = 3) (h3 : q.vertex ⟨r, by omega⟩ = 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+2, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+1, by omega⟩)) :
    (∀ w ∈ [0, 1, 3, 7], sel q w = true) ∧ ∀ s ∈ sp2 lo1 hi1 lo2 hi2, SpecHolds (sel q) s := by
  refine ⟨?_, ?_⟩
  · intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
  · intro s hs
    simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl
    · exact centreI q (r+1) (by omega) 1 1 0 h1 (by rw [h2]; decide) (by rw [h0]; decide)
        cok1.swap a1
    · exact centreI q r (by omega) 3 2 1 h2 (by rw [h3]; decide) (by rw [h1]; decide)
        cok3.swap a2

theorem triF_facts {u3 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3)) (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+1, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+3, by omega⟩)) :
    (∀ w ∈ [0, 1, 3, 7, (flip u3 7).val], sel q w = true) ∧
      ∀ s ∈ sp3 u3 lo1 hi1 lo2 hi2 lo3 hi3, SpecHolds (sel q) s := by
  refine ⟨?_, ?_⟩
  · intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
  · intro s hs
    simp only [sp3, sp2, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact centreI q r (by omega) 1 0 1 h1 (by rw [h0]; decide) (by rw [h2]; decide) cok1 a1
    · exact centreI q (r+1) (by omega) 3 1 2 h2 (by rw [h1]; decide) (by rw [h3]; decide) cok3 a2
    · exact centreI q (r+2) (by omega) 7 2 u3 h3 (by rw [h2]; decide) h4 h7 a3

theorem triB_facts {u3 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3)) (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r+4, by omega⟩ = 0) (h1 : q.vertex ⟨r+3, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+1, by omega⟩ = 7)
    (h4 : q.vertex ⟨r, by omega⟩ = flip u3 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+3, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+1, by omega⟩)) :
    (∀ w ∈ [0, 1, 3, 7, (flip u3 7).val], sel q w = true) ∧
      ∀ s ∈ sp3 u3 lo1 hi1 lo2 hi2 lo3 hi3, SpecHolds (sel q) s := by
  refine ⟨?_, ?_⟩
  · intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
  · intro s hs
    simp only [sp3, sp2, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact centreI q (r+2) (by omega) 1 1 0 h1 (by rw [h2]; decide) (by rw [h0]; decide)
        cok1.swap a1
    · exact centreI q (r+1) (by omega) 3 2 1 h2 (by rw [h3]; decide) (by rw [h1]; decide)
        cok3.swap a2
    · exact centreI q r (by omega) 7 u3 2 h3 h4 (by rw [h2]; decide) h7.swap a3

theorem quadF_facts {u3 u4 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r+5, by omega⟩ = flip u4 (flip u3 7))
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+1, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+3, by omega⟩))
    (a4 : InR lo4 hi4 (localAlpha q ⟨r+4, by omega⟩)) :
    (∀ w ∈ [0, 1, 3, 7, (flip u3 7).val, (flip u4 (flip u3 7)).val], sel q w = true) ∧
      ∀ s ∈ sp4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4, SpecHolds (sel q) s := by
  refine ⟨?_, ?_⟩
  · intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
    · exact sel_at q _ h5
  · intro s hs
    simp only [sp4, sp3, sp2, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact centreI q r (by omega) 1 0 1 h1 (by rw [h0]; decide) (by rw [h2]; decide) cok1 a1
    · exact centreI q (r+1) (by omega) 3 1 2 h2 (by rw [h1]; decide) (by rw [h3]; decide) cok3 a2
    · exact centreI q (r+2) (by omega) 7 2 u3 h3 (by rw [h2]; decide) h4 h7 a3
    · exact centreI q (r+3) (by omega) (flip u3 7) u3 u4 h4
        (by rw [h3, flip_twice]) h5 hx a4

theorem quadB_facts {u3 u4 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r+5, by omega⟩ = 0) (h1 : q.vertex ⟨r+4, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+3, by omega⟩ = 3) (h3 : q.vertex ⟨r+2, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+1, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r, by omega⟩ = flip u4 (flip u3 7))
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+4, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+3, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+2, by omega⟩))
    (a4 : InR lo4 hi4 (localAlpha q ⟨r+1, by omega⟩)) :
    (∀ w ∈ [0, 1, 3, 7, (flip u3 7).val, (flip u4 (flip u3 7)).val], sel q w = true) ∧
      ∀ s ∈ sp4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4, SpecHolds (sel q) s := by
  refine ⟨?_, ?_⟩
  · intro w hw'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sel_at q _ h0
    · exact sel_at q _ h1
    · exact sel_at q _ h2
    · exact sel_at q _ h3
    · exact sel_at q _ h4
    · exact sel_at q _ h5
  · intro s hs
    simp only [sp4, sp3, sp2, List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact centreI q (r+3) (by omega) 1 1 0 h1 (by rw [h2]; decide) (by rw [h0]; decide)
        cok1.swap a1
    · exact centreI q (r+2) (by omega) 3 2 1 h2 (by rw [h3]; decide) (by rw [h1]; decide)
        cok3.swap a2
    · exact centreI q (r+1) (by omega) 7 u3 2 h3 h4 (by rw [h2]; decide) h7.swap a3
    · exact centreI q r (by omega) (flip u3 7) u4 u3 h4 h5
        (by rw [h3, flip_twice]) hx.swap a4

/-! ### Refuted windows do not occur -/

theorem fixv {q' : Snake m} {W : List Coord}
    (hfix : ∀ i, BitsIn W (q.vertex i) → q'.vertex i = q.vertex i) {i : Fin (m+1)} {v : Vertex}
    (h : q.vertex i = v) (hb : BitsIn W v) : q'.vertex i = v := by
  rw [hfix i (h ▸ hb), h]

theorem inR_tr {q' : Snake m} (hal : ∀ k, localAlpha q' k = localAlpha q k) {lo hi : Nat}
    {k : Fin (m+1)} (a : InR lo hi (localAlpha q k)) : InR lo hi (localAlpha q' k) := by
  rw [hal]; exact a

theorem duoF {lo1 hi1 lo2 hi2 : Nat} (hR : Q2 lo1 hi1 lo2 hi2) (r : Nat) (hr : r + 3 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+1, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩)) : False := by
  rcases hR with ⟨T, F, hF, hok, hc, hT, hw⟩ | hR
  · obtain ⟨hwin, hsp⟩ := duoF_facts q r hr h0 h1 h2 h3 a1 a2
    exact win_false q (by omega) hF hok hc hT (hw ▸ hwin) hsp
  · exact refL_false q (by omega) hR fun q' hfix hal =>
      duoF_facts q' r hr (fixv q hfix h0 bits0) (fixv q hfix h1 bits1) (fixv q hfix h2 bits3)
        (fixv q hfix h3 bits7) (inR_tr q hal a1) (inR_tr q hal a2)

theorem duoB {lo1 hi1 lo2 hi2 : Nat} (hR : Q2 lo1 hi1 lo2 hi2) (r : Nat) (hr : r + 3 ≤ m)
    (h0 : q.vertex ⟨r+3, by omega⟩ = 0) (h1 : q.vertex ⟨r+2, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+1, by omega⟩ = 3) (h3 : q.vertex ⟨r, by omega⟩ = 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+2, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+1, by omega⟩)) : False := by
  rcases hR with ⟨T, F, hF, hok, hc, hT, hw⟩ | hR
  · obtain ⟨hwin, hsp⟩ := duoB_facts q r hr h0 h1 h2 h3 a1 a2
    exact win_false q (by omega) hF hok hc hT (hw ▸ hwin) hsp
  · exact refL_false q (by omega) hR fun q' hfix hal =>
      duoB_facts q' r hr (fixv q hfix h0 bits0) (fixv q hfix h1 bits1) (fixv q hfix h2 bits3)
        (fixv q hfix h3 bits7) (inR_tr q hal a1) (inR_tr q hal a2)

theorem triF {u3 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (hR : Q3 u3 lo1 hi1 lo2 hi2 lo3 hi3) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+1, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+3, by omega⟩)) : False := by
  rcases hR with ⟨T, F, hF, hok, hc, hT, hw⟩ | hR
  · obtain ⟨hwin, hsp⟩ := triF_facts q h7 r hr h0 h1 h2 h3 h4 a1 a2 a3
    exact win_false q (by omega) hF hok hc hT (hw ▸ hwin) hsp
  · have hs : ∀ c ∈ ([0, 1, 2] : List Coord), c ∈ ([0, 1, 2, u3] : List Coord) := by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; tauto
    have b7 := bitsIn_mono bits7 hs
    exact refL_false q (by omega) hR fun q' hfix hal =>
      triF_facts q' h7 r hr (fixv q hfix h0 (bitsIn_mono bits0 hs)) (fixv q hfix h1 (bitsIn_mono bits1 hs))
        (fixv q hfix h2 (bitsIn_mono bits3 hs)) (fixv q hfix h3 b7)
        (fixv q hfix h4 (bitsIn_flip b7 (by simp))) (inR_tr q hal a1) (inR_tr q hal a2)
        (inR_tr q hal a3)

theorem triB {u3 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 : Nat}
    (hR : Q3 u3 lo1 hi1 lo2 hi2 lo3 hi3) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r+4, by omega⟩ = 0) (h1 : q.vertex ⟨r+3, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+1, by omega⟩ = 7)
    (h4 : q.vertex ⟨r, by omega⟩ = flip u3 7)
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+3, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+1, by omega⟩)) : False := by
  rcases hR with ⟨T, F, hF, hok, hc, hT, hw⟩ | hR
  · obtain ⟨hwin, hsp⟩ := triB_facts q h7 r hr h0 h1 h2 h3 h4 a1 a2 a3
    exact win_false q (by omega) hF hok hc hT (hw ▸ hwin) hsp
  · have hs : ∀ c ∈ ([0, 1, 2] : List Coord), c ∈ ([0, 1, 2, u3] : List Coord) := by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; tauto
    have b7 := bitsIn_mono bits7 hs
    exact refL_false q (by omega) hR fun q' hfix hal =>
      triB_facts q' h7 r hr (fixv q hfix h0 (bitsIn_mono bits0 hs)) (fixv q hfix h1 (bitsIn_mono bits1 hs))
        (fixv q hfix h2 (bitsIn_mono bits3 hs)) (fixv q hfix h3 b7)
        (fixv q hfix h4 (bitsIn_flip b7 (by simp))) (inR_tr q hal a1) (inR_tr q hal a2)
        (inR_tr q hal a3)

theorem quadF {u3 u4 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (hR : Q4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4)
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r+5, by omega⟩ = flip u4 (flip u3 7))
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+1, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+2, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+3, by omega⟩))
    (a4 : InR lo4 hi4 (localAlpha q ⟨r+4, by omega⟩)) : False := by
  rcases hR with ⟨T, F, hF, hok, hc, hT, hw⟩ | hR
  · obtain ⟨hwin, hsp⟩ := quadF_facts q h7 hx r hr h0 h1 h2 h3 h4 h5 a1 a2 a3 a4
    exact win_false q (by omega) hF hok hc hT (hw ▸ hwin) hsp
  · have hs : ∀ c ∈ ([0, 1, 2] : List Coord), c ∈ ([0, 1, 2, u3, u4] : List Coord) := by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; tauto
    have b7 := bitsIn_mono bits7 hs
    have b4 := bitsIn_flip b7 (u := u3) (by simp)
    exact refL_false q (by omega) hR fun q' hfix hal =>
      quadF_facts q' h7 hx r hr (fixv q hfix h0 (bitsIn_mono bits0 hs))
        (fixv q hfix h1 (bitsIn_mono bits1 hs)) (fixv q hfix h2 (bitsIn_mono bits3 hs))
        (fixv q hfix h3 b7) (fixv q hfix h4 b4) (fixv q hfix h5 (bitsIn_flip b4 (by simp)))
        (inR_tr q hal a1) (inR_tr q hal a2) (inR_tr q hal a3) (inR_tr q hal a4)

theorem quadB {u3 u4 : Coord} {lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : Nat}
    (hR : Q4 u3 u4 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4)
    (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r+5, by omega⟩ = 0) (h1 : q.vertex ⟨r+4, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+3, by omega⟩ = 3) (h3 : q.vertex ⟨r+2, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+1, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r, by omega⟩ = flip u4 (flip u3 7))
    (a1 : InR lo1 hi1 (localAlpha q ⟨r+4, by omega⟩))
    (a2 : InR lo2 hi2 (localAlpha q ⟨r+3, by omega⟩))
    (a3 : InR lo3 hi3 (localAlpha q ⟨r+2, by omega⟩))
    (a4 : InR lo4 hi4 (localAlpha q ⟨r+1, by omega⟩)) : False := by
  rcases hR with ⟨T, F, hF, hok, hc, hT, hw⟩ | hR
  · obtain ⟨hwin, hsp⟩ := quadB_facts q h7 hx r hr h0 h1 h2 h3 h4 h5 a1 a2 a3 a4
    exact win_false q (by omega) hF hok hc hT (hw ▸ hwin) hsp
  · have hs : ∀ c ∈ ([0, 1, 2] : List Coord), c ∈ ([0, 1, 2, u3, u4] : List Coord) := by
      intro c hc; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc ⊢; tauto
    have b7 := bitsIn_mono bits7 hs
    have b4 := bitsIn_flip b7 (u := u3) (by simp)
    exact refL_false q (by omega) hR fun q' hfix hal =>
      quadB_facts q' h7 hx r hr (fixv q hfix h0 (bitsIn_mono bits0 hs))
        (fixv q hfix h1 (bitsIn_mono bits1 hs)) (fixv q hfix h2 (bitsIn_mono bits3 hs))
        (fixv q hfix h3 b7) (fixv q hfix h4 b4) (fixv q hfix h5 (bitsIn_flip b4 (by simp)))
        (inR_tr q hal a1) (inR_tr q hal a2) (inR_tr q hal a3) (inR_tr q hal a4)

/-! ### Flagged windows are refuted -/

theorem duoF_tab {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P2 x) (ht : tab2 [0, 1, 2] L = true)
    (r : Nat) (hr : r + 3 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (hw : wforb1 [0, 1, 2] [sym (localAlpha q ⟨r+1, by omega⟩),
      sym (localAlpha q ⟨r+2, by omega⟩)] = true) : False := by
  obtain ⟨lo1, hi1, lo2, hi2, hm, a1, a2⟩ := tab2_spec ht hw
  exact duoF q (hL _ hm) r hr h0 h1 h2 h3 a1 a2

theorem duoB_tab {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P2 x) (ht : tab2 [0, 1, 2] L = true)
    (r : Nat) (hr : r + 3 ≤ m)
    (h0 : q.vertex ⟨r+3, by omega⟩ = 0) (h1 : q.vertex ⟨r+2, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+1, by omega⟩ = 3) (h3 : q.vertex ⟨r, by omega⟩ = 7)
    (hw : wforb1 [0, 1, 2] [sym (localAlpha q ⟨r+2, by omega⟩),
      sym (localAlpha q ⟨r+1, by omega⟩)] = true) : False := by
  obtain ⟨lo1, hi1, lo2, hi2, hm, a1, a2⟩ := tab2_spec ht hw
  exact duoB q (hL _ hm) r hr h0 h1 h2 h3 a1 a2

theorem triF_tab {u3 : Coord} {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P3 u3 x)
    (ht : tab3 [0, 1, 2, u3.val] L = true) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (hw : wforb1 [0, 1, 2, u3.val] [sym (localAlpha q ⟨r+1, by omega⟩),
      sym (localAlpha q ⟨r+2, by omega⟩), sym (localAlpha q ⟨r+3, by omega⟩)] = true) : False := by
  obtain ⟨lo1, hi1, lo2, hi2, lo3, hi3, hm, a1, a2, a3⟩ := tab3_spec ht hw
  exact triF q (hL _ hm) h7 r hr h0 h1 h2 h3 h4 a1 a2 a3

theorem triB_tab {u3 : Coord} {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P3 u3 x)
    (ht : tab3 [0, 1, 2, u3.val] L = true) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (r : Nat) (hr : r + 4 ≤ m)
    (h0 : q.vertex ⟨r+4, by omega⟩ = 0) (h1 : q.vertex ⟨r+3, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+1, by omega⟩ = 7)
    (h4 : q.vertex ⟨r, by omega⟩ = flip u3 7)
    (hw : wforb1 [0, 1, 2, u3.val] [sym (localAlpha q ⟨r+3, by omega⟩),
      sym (localAlpha q ⟨r+2, by omega⟩), sym (localAlpha q ⟨r+1, by omega⟩)] = true) : False := by
  obtain ⟨lo1, hi1, lo2, hi2, lo3, hi3, hm, a1, a2, a3⟩ := tab3_spec ht hw
  exact triB q (hL _ hm) h7 r hr h0 h1 h2 h3 h4 a1 a2 a3

theorem quadF_tab {u3 u4 : Coord} {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P4 u3 u4 x)
    (ht : tab4 [0, 1, 2, u3.val, u4.val] L = true) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r, by omega⟩ = 0) (h1 : q.vertex ⟨r+1, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+2, by omega⟩ = 3) (h3 : q.vertex ⟨r+3, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+4, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r+5, by omega⟩ = flip u4 (flip u3 7))
    (hw : wforb1 [0, 1, 2, u3.val, u4.val] [sym (localAlpha q ⟨r+1, by omega⟩),
      sym (localAlpha q ⟨r+2, by omega⟩), sym (localAlpha q ⟨r+3, by omega⟩),
      sym (localAlpha q ⟨r+4, by omega⟩)] = true) : False := by
  obtain ⟨lo1, hi1, lo2, hi2, lo3, hi3, lo4, hi4, hm, a1, a2, a3, a4⟩ := tab4_spec ht hw
  exact quadF q (hL _ hm) h7 hx r hr h0 h1 h2 h3 h4 h5 a1 a2 a3 a4

theorem quadB_tab {u3 u4 : Coord} {L : List (List (Nat × Nat))} (hL : ∀ x ∈ L, P4 u3 u4 x)
    (ht : tab4 [0, 1, 2, u3.val, u4.val] L = true) (h7 : CornerOK 7 2 u3 (cornerVerts 7 2 u3))
    (hx : CornerOK (flip u3 7).val u3 u4 (cornerVerts (flip u3 7).val u3 u4))
    (r : Nat) (hr : r + 5 ≤ m)
    (h0 : q.vertex ⟨r+5, by omega⟩ = 0) (h1 : q.vertex ⟨r+4, by omega⟩ = 1)
    (h2 : q.vertex ⟨r+3, by omega⟩ = 3) (h3 : q.vertex ⟨r+2, by omega⟩ = 7)
    (h4 : q.vertex ⟨r+1, by omega⟩ = flip u3 7)
    (h5 : q.vertex ⟨r, by omega⟩ = flip u4 (flip u3 7))
    (hw : wforb1 [0, 1, 2, u3.val, u4.val] [sym (localAlpha q ⟨r+4, by omega⟩),
      sym (localAlpha q ⟨r+3, by omega⟩), sym (localAlpha q ⟨r+2, by omega⟩),
      sym (localAlpha q ⟨r+1, by omega⟩)] = true) : False := by
  obtain ⟨lo1, hi1, lo2, hi2, lo3, hi3, lo4, hi4, hm, a1, a2, a3, a4⟩ := tab4_spec ht hw
  exact quadB q (hL _ hm) h7 hx r hr h0 h1 h2 h3 h4 h5 a1 a2 a3 a4

/-- A window whose table list is empty is never flagged. -/
theorem none4 {c : List Nat} (ht : tab4 c [] = true) {a1 a2 a3 a4 : Nat}
    (hw : wforb1 c [sym a1, sym a2, sym a3, sym a4] = true) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, hm, -⟩ := tab4_spec ht hw
  exact List.not_mem_nil hm

end

end D239
