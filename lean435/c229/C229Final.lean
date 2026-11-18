module

public import C230Final

@[expose] public section

/-!
# Conditional bounds 229 .. 224 from the K7 chain and a higher uniform corner-share floor (milestone 38)

The 230 assembly (`C230Final`) with the share level as a parameter.  Premises:

* `AllTab tab230`: the 58,817 window exclusions of the K7R34C7W16 chain, exactly the premise of the 230
  theorem (walk `89 m ≤ 19 Σ α + 678`, `C230.walk230`);
* `AllShareK K shares230`: for each of the 132 canonical 8-direction shapes `s`, the certificate
  `RefutedShare (winOf s) [(1,21)] x 7 12 K`, i.e. corner share (`coreShare 12`) at least `K + 1` on the
  7 centres of every window of that shape, counts free.  `K = 29` is the share premise of 230.

With `X = K + 1`, `core_charge_sum_le 12` and `α_0, α_m ≥ 4` give

    (126672 + 19 X) m ≤ 29387736 + 133 X          (`upper_of_tables_shareK`),

so `m ≤ 229` from `X ≥ 60`, `228` from `91`, `227` from `121`, `226` from `152`, `225` from `183` and `224`
from `215`.  These are CONDITIONAL statements: no premise at a level above 30 is certified, and the levels
of the lower bounds may be false (see milestones/38-220-conditional/README.md for the solver evidence).
-/

namespace Snake9.C230
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow Snake9.WindowAggregate Finset

/-- Every listed 8-direction shape has corner share at least `K + 1` on its 7 centres (counts free). -/
def AllShareK (K : Nat) : List (List Nat) → Prop
  | [] => True
  | s :: l => RefutedShare (winOf s) free7 12 K ∧ AllShareK K l

theorem AllShareK.mem {K : Nat} : ∀ {L : List (List Nat)}, AllShareK K L → ∀ s ∈ L,
    RefutedShare (winOf s) free7 12 K
  | [], _, _, hs => absurd hs List.not_mem_nil
  | _ :: _, ⟨h, hL⟩, s, hs => by
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h
    · exact AllShareK.mem hL s hs

/-- The share premise of the 230 theorem is the level `K = 29`. -/
theorem allShareK_of_allShareL : ∀ {L : List (List Nat)}, AllShareL L → AllShareK 29 L
  | [], _ => trivial
  | _ :: _, ⟨h, hL⟩ => ⟨h, allShareK_of_allShareL hL⟩

section Walk
variable {m : Nat} (p : Snake m)

theorem window_shareK {K : Nat} (hS : AllShareK K shares230) (hm : 3 ≤ m) (j : Nat) (hj : j + 8 ≤ m) :
    K + 1 ≤ ∑ i ∈ range 7, coreShare 12 p (j + i + 1) := by
  have hpos := coreAlpha_pos p hm
  have hsh : canon (dsOf p j 8) ∈ shares230 := by
    rw [dsOf_eq_blockList p hj, show shares230 = shapes8 from rfl]
    exact window_shape_mem (by decide) cover8 p j hj
  have href := hS.mem _ hsh
  have hlen := length_dsOf p j 8
  have hmem : ∀ k, k < 8 → (dsOf p j 8).getD k 0 ∈ seenAfter [] (dsOf p j 8) := by
    intro k hk
    apply mem_seenAfter
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have h := refuted_share_dir_iv p href j (u := seenAfter [] (dsOf p j 8)) (by rw [length_canon, length_dsOf]; rfl)
    (by rw [length_canon, length_dsOf]; omega) (seenAfter_nodup [] _ List.nodup_nil) ?_ ?_ ?_
  · simp only [free7, List.length_cons, List.length_nil, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    omega
  · intro d hd
    rcases mem_seenAfter_cases [] _ d hd with h | h
    · simp at h
    · simp only [dsOf, List.mem_map, List.mem_range] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact dir_lt p (by omega)
  · intro k hk
    rw [length_canon] at hk
    have e : (canon (dsOf p j 8)).getD k 0 = idx (seenAfter [] (dsOf p j 8)) ((dsOf p j 8).getD k 0) := by
      rw [canon_eq_map, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl
    rw [e]
    refine ⟨idx_lt_of_mem _ _ (hmem k (by omega)), ?_⟩
    rw [getD_idx _ _ (hmem k (by omega)), getD_dsOf p (by omega)]
  · intro i hi
    have hi7 : i < 7 := by simpa [free7] using hi
    have e : free7.getD i (0, 21) = (1, 21) := by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e]
    exact ⟨hpos _ (by omega) (by omega), coreAlpha_le_21 p (by omega) (by omega)⟩

/-- The K7 walk, the corner identity and a uniform corner-share floor `K + 1` on 7-centre windows. -/
theorem upper_of_tables_shareK {K : Nat} (p : Snake m) (hm : 9 ≤ m) (hT : AllTab tab230)
    (hS : AllShareK K shares230) :
    (126672 + 19 * (K + 1)) * m ≤ 29387736 + 133 * (K + 1) := by
  have hwalk := walk230 p hT (by omega)
  obtain ⟨h0, h1, _, _, _⟩ := countSeq_facts p (by omega)
  rw [countSeq_eq_coreAlpha_le p 0 (by omega)] at h0
  rw [countSeq_eq_coreAlpha_le p m (by omega)] at h1
  have hid := core_charge_sum_le 12 p (by omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, alpha_split p (by omega)] at hid
  have hw : (K + 1) * (m - 7) ≤ ∑ j ∈ range (m - 7), ∑ i ∈ range 7, coreShare 12 p (j + i + 1) := by
    have := Finset.card_nsmul_le_sum (range (m - 7)) (fun j => ∑ i ∈ range 7, coreShare 12 p (j + i + 1)) (K + 1)
      (fun j hj => window_shareK p hS (by omega) j (by rw [Finset.mem_range] at hj; omega))
    simpa [mul_comm] using this
  have hsw := sum_windows_le p (by omega)
  have e1 : (K + 1) * (m - 7) + 7 * (K + 1) = (K + 1) * m := by
    rw [Nat.mul_comm 7 (K + 1), ← Nat.mul_add]
    congr 1
    omega
  have e2 : (126672 + 19 * (K + 1)) * m = 126672 * m + 19 * ((K + 1) * m) := by ring
  rw [e2]
  generalize (K + 1) * m = t at e1 ⊢
  generalize (K + 1) * (m - 7) = w at e1 hw
  generalize K + 1 = X at e1 ⊢
  omega

end Walk

end Snake9.C230

namespace Snake9
open C230

/-- The general conditional statement: the premises of the K7 route at share level `K + 1`. -/
theorem upper_of_refutedK7_share {K : Nat} (hT : AllTab tab230) (hS : AllShareK K shares230) :
    ∀ {m : Nat}, Snake m → 9 ≤ m → (126672 + 19 * (K + 1)) * m ≤ 29387736 + 133 * (K + 1) :=
  fun p hm => upper_of_tables_shareK p hm hT hS

/-- Conditional bound 229: the K7 window table and a uniform 7-window corner share of at least 60. -/
theorem upper_229_of_refutedK7 (hT : AllTab tab230) (hS : AllShareK 59 shares230) :
    ∀ {m : Nat}, Snake m → m ≤ 229 := by
  intro m p
  by_cases hm : m < 9
  · omega
  have := upper_of_tables_shareK p (by omega) hT hS
  omega

/-- Conditional bound 228: uniform 7-window corner share of at least 91. -/
theorem upper_228_of_refutedK7 (hT : AllTab tab230) (hS : AllShareK 90 shares230) :
    ∀ {m : Nat}, Snake m → m ≤ 228 := by
  intro m p
  by_cases hm : m < 9
  · omega
  have := upper_of_tables_shareK p (by omega) hT hS
  omega

/-- Conditional bound 227: uniform 7-window corner share of at least 121. -/
theorem upper_227_of_refutedK7 (hT : AllTab tab230) (hS : AllShareK 120 shares230) :
    ∀ {m : Nat}, Snake m → m ≤ 227 := by
  intro m p
  by_cases hm : m < 9
  · omega
  have := upper_of_tables_shareK p (by omega) hT hS
  omega

/-- The 230 theorem again, as the instance `K = 29` (a check of the parametrised count). -/
theorem upper_230_of_refutedK7' (hT : AllTab tab230) (hS : AllShareL shares230) :
    ∀ {m : Nat}, Snake m → m ≤ 230 := by
  intro m p
  by_cases hm : m < 9
  · omega
  have := upper_of_tables_shareK p (by omega) hT (allShareK_of_allShareL hS)
  omega

end Snake9
