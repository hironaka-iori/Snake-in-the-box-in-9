import DirectionWindowBridge
import WindowAutomatonSym

/-!
Count-window normalization with an arbitrary lumping threshold. In the 231 chain,
`K = 8`: symbols 0..7 are exact and symbol 8 means the interval [8,21].
The older `refuted_dir` uses threshold 6 and cannot instantiate this interface.
Local refutations remain explicit premises until the certificate family is checked.
-/
namespace Snake9.CountWindowBridge
open LocalWindow DirectionWindow WindowAutomaton
set_option maxHeartbeats 1000000

def boundK (K s : Nat) : Nat × Nat := if s < K then (s, s) else (K, 21)

def boundsK (K : Nat) (syms : List Nat) : List (Nat × Nat) := syms.map (boundK K)

theorem boundK_symK (K a : Nat) (ha : a ≤ 21) :
    (boundK K (symK K a)).1 ≤ a ∧ a ≤ (boundK K (symK K a)).2 := by
  by_cases h : a < K
  · simp [boundK, symK, Nat.min_eq_left (Nat.le_of_lt h), h]
  · have hk : K ≤ a := by omega
    simp [boundK, symK, Nat.min_eq_right hk, hk, ha]

theorem getD_boundsK (K : Nat) {syms : List Nat} {i : Nat} (hi : i < syms.length) :
    (boundsK K syms).getD i (0, 21) = boundK K (syms.getD i 0) := by
  simp [boundsK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- Canonical direction labels supply a valid cube automorphism for any interval
list, including lists with a threshold different from the old six-symbol table. -/
theorem refuted_canonical {m : Nat} (p : Snake m) (r n : Nat)
    (bounds : List (Nat × Nat)) (hlen : bounds.length + 1 = n) (hr : r + n ≤ m)
    (href : Refuted (winOf (canon (dsOf p r n))) bounds)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ (bounds.getD i (0, 21)).2) : False := by
  let u := seenAfter [] (dsOf p r n)
  have hu : u.Nodup := seenAfter_nodup [] _ List.nodup_nil
  have hu9 : ∀ d ∈ u, d < 9 := by
    intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨j, hj, rfl⟩ := h
      exact dir_lt p (by omega)
  have huLen : u.length ≤ 9 := by
    have := nodup_length_le_of_subset (l' := List.range 9) hu
      (fun x hx => List.mem_range.2 (hu9 x hx))
    simpa using this
  have hp := mkPerm_spec hu hu9 huLen
  have hlenDs := length_dsOf p r n
  have hmem : ∀ j, j < n → (dsOf p r n).getD j 0 ∈ u := by
    intro j hj
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  refine refuted_bridge p (mkPerm u) r href (canon_winOf _) (by rw [length_canon, hlenDs]; exact hlen)
    (by rw [length_canon, hlenDs]; exact hr) ?_ hb
  intro j hj
  rw [length_canon, hlenDs] at hj
  have he : (canon (dsOf p r n)).getD j 0 = idx u ((dsOf p r n).getD j 0) := by
    rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  rw [he, ← getD_dsOf p hj]
  have hperm := hp _ (idx_lt_of_mem _ _ (hmem j hj))
  rw [getD_idx u _ (hmem j hj)] at hperm
  exact hperm

def symsK {m : Nat} (p : Snake m) (K r n : Nat) : List Nat :=
  (List.range (n - 1)).map (fun i => symK K (coreAlpha p (r + i + 1)))

theorem symsK_length {m : Nat} (p : Snake m) (K r n : Nat) :
    (symsK p K r n).length = n - 1 := by simp [symsK]

theorem symsK_le {m : Nat} (p : Snake m) (K r n : Nat) :
    ∀ s ∈ symsK p K r n, s ≤ K := by
  intro s hs
  simp only [symsK, List.mem_map] at hs
  obtain ⟨i, _, rfl⟩ := hs
  exact symK_le_K _ _

theorem getD_symsK {m : Nat} (p : Snake m) (K r n i : Nat) (hi : i < n - 1) :
    (symsK p K r n).getD i 0 = symK K (coreAlpha p (r + i + 1)) := by
  simp [symsK, List.getD_eq_getElem?_getD, hi]

theorem refuted_count_window {m : Nat} (p : Snake m) (K r n : Nat)
    (hn : 1 ≤ n) (hr : r + n ≤ m)
    (href : Refuted (winOf (canon (dsOf p r n))) (boundsK K (symsK p K r n))) : False := by
  refine refuted_canonical p r n _ (by simp [boundsK, symsK]; omega) hr href ?_
  intro i hi
  have hi' : i < (symsK p K r n).length := by simpa [boundsK] using hi
  rw [getD_boundsK K hi', getD_symsK p K r n i (by simpa [symsK] using hi')]
  exact boundK_symK K _ (coreAlpha_le_21 p (by omega) (by simp [symsK] at hi'; omega))

theorem symsK_rev {m : Nat} (p : Snake m) (K r n : Nat) (hr : r + n ≤ m) :
    symsK (revSnake p) K (m - r - n) n = (symsK p K r n).reverse := by
  apply List.ext_getElem
  · simp [symsK]
  · intro i h1 h2
    simp only [symsK, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range]
    simp only [symsK, List.length_map, List.length_range] at h1
    rw [coreAlpha_rev p (by omega)]
    congr 2
    omega

/-- Each certificate interval contains the full interpretation of the count
symbol. In particular [6,21] may cover symbols 6, 7, and the whole class [8,21]. -/
def coversK (K : Nat) : List (Nat × Nat) → List Nat → Bool
  | [], [] => true
  | b :: bs, s :: ss =>
      decide (b.1 ≤ (boundK K s).1 ∧ (boundK K s).2 ≤ b.2) && coversK K bs ss
  | _, _ => false

theorem coversK_length (K : Nat) : ∀ (bs : List (Nat × Nat)) (ss : List Nat),
    coversK K bs ss = true → bs.length = ss.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [coversK] at h
  | _ :: _, [], h => by simp [coversK] at h
  | _ :: bs, _ :: ss, h => by
    have htail := (Bool.and_eq_true_iff.1 h).2
    simp only [List.length_cons, coversK_length K bs ss htail]

theorem coversK_getD (K : Nat) : ∀ (bs : List (Nat × Nat)) (ss : List Nat),
    coversK K bs ss = true → ∀ i, i < ss.length →
      (bs.getD i (0, 21)).1 ≤ (boundK K (ss.getD i 0)).1 ∧
      (boundK K (ss.getD i 0)).2 ≤ (bs.getD i (0, 21)).2
  | [], [], _, _, hi => by simp at hi
  | [], _ :: _, h, _, _ => by simp [coversK] at h
  | _ :: _, [], h, _, _ => by simp [coversK] at h
  | b :: bs, s :: ss, h, 0, _ => of_decide_eq_true (Bool.and_eq_true_iff.1 h).1
  | b :: bs, s :: ss, h, i + 1, hi => by
    simp only [List.getD_cons_succ]
    exact coversK_getD K bs ss (Bool.and_eq_true_iff.1 h).2 i (by simpa using hi)

theorem refuted_cover_window {m : Nat} (p : Snake m) (K r n : Nat)
    (hn : 1 ≤ n) (hr : r + n ≤ m) (bounds : List (Nat × Nat))
    (href : Refuted (winOf (canon (dsOf p r n))) bounds)
    (hc : coversK K bounds (symsK p K r n) = true) : False := by
  have hl := coversK_length K _ _ hc
  have hls := symsK_length p K r n
  refine refuted_canonical p r n bounds (by omega) hr href ?_
  intro i hi
  have hi' : i < n - 1 := by omega
  have hc' := coversK_getD K _ _ hc i (by omega)
  rw [getD_symsK p K r n i hi'] at hc'
  have hb := boundK_symK K (coreAlpha p (r + i + 1))
    (coreAlpha_le_21 p (by omega) (by omega))
  exact ⟨Nat.le_trans hc'.1 hb.1, Nat.le_trans hb.2 hc'.2⟩

abbrev IntervalKey := List Nat × List (Nat × Nat)

def intervalHit (K : Nat) (keys : List IntervalKey) (ds syms : List Nat) : Bool :=
  keys.any fun key => decide (canon ds = key.1) && coversK K key.2 syms

def AllRefutedIntervals (keys : List IntervalKey) : Prop :=
  ∀ key ∈ keys, Refuted (winOf key.1) key.2

theorem no_interval_hit {K : Nat} {keys : List IntervalKey} (h : AllRefutedIntervals keys)
    {m : Nat} (p : Snake m) (r n : Nat) (hn : 1 ≤ n) (hr : r + n ≤ m) :
    intervalHit K keys (dsOf p r n) (symsK p K r n) = false := by
  cases he : intervalHit K keys (dsOf p r n) (symsK p K r n)
  · rfl
  · exfalso
    obtain ⟨key, hk, heq⟩ := List.any_eq_true.1 he
    have heq' : canon (dsOf p r n) = key.1 := of_decide_eq_true (Bool.and_eq_true_iff.1 heq).1
    apply refuted_cover_window p K r n hn hr key.2
    · rw [heq']; exact h key hk
    · exact (Bool.and_eq_true_iff.1 heq).2

theorem no_reverse_interval_hit {K : Nat} {keys : List IntervalKey} (h : AllRefutedIntervals keys)
    {m : Nat} (p : Snake m) (r n : Nat) (hn : 1 ≤ n) (hr : r + n ≤ m) :
    intervalHit K keys (dsOf p r n).reverse (symsK p K r n).reverse = false := by
  rw [← dsOf_rev p r n hr, ← symsK_rev p K r n hr]
  exact no_interval_hit h (revSnake p) (m - r - n) n hn (by omega)

def AllRefutedK (K : Nat) (keys : List (List Nat × List Nat)) : Prop :=
  ∀ key ∈ keys, Refuted (winOf key.1) (boundsK K key.2)

/-- A checked local family excludes precisely its keys on arbitrary snake windows.
This theorem does not assert that an unverified family has been supplied. -/
theorem no_key {K : Nat} {keys : List (List Nat × List Nat)} (h : AllRefutedK K keys)
    {m : Nat} (p : Snake m) (r n : Nat) (hn : 1 ≤ n) (hr : r + n ≤ m) :
    (canon (dsOf p r n), symsK p K r n) ∉ keys := by
  intro hmem
  exact refuted_count_window p K r n hn hr (h _ hmem)

#print axioms boundK_symK
#print axioms refuted_canonical
#print axioms refuted_count_window
#print axioms symsK_rev
#print axioms refuted_cover_window
#print axioms no_interval_hit
#print axioms no_reverse_interval_hit
#print axioms no_key
end Snake9.CountWindowBridge
