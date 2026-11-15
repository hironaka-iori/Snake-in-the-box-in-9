import AggregateDirection6SConditional
import DirectionWindowBridge6SC
import CombinedShareToy

/-!
# Bounds from a share-weighted six-centre automaton with context shares (generic)

Milestone 35 (`milestones/35-231-lean/DESIGN.md`).  The copy of `AggregateDirection6SConditional`
(unchanged, audited 233 chain) for `T : Tables6SC`:

1. `total_bound6SC` telescopes the step inequality with the weight `120 sym a(n+7) + S5C n`;
2. `S5C n ≤ Σ_{j=n+3}^{n+7} coreShare 12 p j`: the share part by `share_windows6S` (share
   certificates and floors, unchanged), the ctx 7 / ctx 8 parts by `ctx_windows6SC`;
3. `core_charge_sum_le 12 p` and `Combined.combined_bound`, unchanged, give
   `(num + 4200 den) m ≤ 1099800 den + 7 num + (2^bits - 1)`.

`upper_of_windows6SC` takes the window bound as a premise; `upper_of_refuted6SC` takes the
certificate statements (plain k6 and H8 keys, 5-window share keys, ctx 7 keys, ctx 8 keys), the
floors and the kernel checks; `upper_of_refuted6SC_noShare` is the variant for a zero 5-window
share table (no share keys, no floors; toy instances).
-/

namespace Snake9
open SquareIncidence Finset Classical WindowAggregate WindowAutomaton LocalWindow
  DirectionWindow6 DirectionWindow6S DirectionWindow6SC
noncomputable section
set_option maxHeartbeats 1600000

/-- The bound from the window premises and the share window bounds. -/
theorem upper_of_windows6SC (T : Tables6SC) (hT : StepOK6SC T) {m : Nat} (p : Snake m)
    (hw : Windows6S T.s (pathDir p) (coreAlpha p) m)
    (hS : (∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j) → ∀ n, n + 8 ≤ m →
      S5C T (win8s6 (pathDir p) n) (syms6s6 (coreAlpha p) n) ≤
        coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) +
          coreShare 12 p (n+6) + coreShare 12 p (n+7)) :
    (T.s.k6.num + 4200 * T.s.k6.den) * m ≤
      1099800 * T.s.k6.den + 7 * T.s.k6.num + (2 ^ T.s.k6.bits - 1) := by
  by_cases hm : m < 7
  · have : (T.s.k6.num + 4200 * T.s.k6.den) * m ≤ (T.s.k6.num + 4200 * T.s.k6.den) * 6 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨h0, h1, hpos, _, _⟩ := countSeq_facts p (by omega)
  have hpos' : ∀ j, 1 ≤ j → j + 1 ≤ m → 1 ≤ coreAlpha p j := by
    intro j hj hjm
    have := hpos (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega, countSeq_eq_coreAlpha_le p j (by omega)] at this
    exact this
  have htel := total_bound6SC T hT (pathDir p) (coreAlpha p) m (by omega) hpos'
    (fun i hi => snake_inducedPattern_block p i 8 hi) hw
  have hid := core_charge_sum_le 12 p (by omega)
  rw [← rsum_eq_sum] at hid
  rw [countSeq_eq_coreAlpha_le p 0 (by omega)] at h0
  rw [countSeq_eq_coreAlpha_le p m (by omega)] at h1
  exact Combined.combined_bound T.s.k6.num T.s.k6.den (2 ^ T.s.k6.bits - 1) m (coreAlpha p)
    (coreShare 12 p) (fun j => sym (coreAlpha p j))
    (fun n => S5C T (win8s6 (pathDir p) n) (syms6s6 (coreAlpha p) n))
    (by omega) htel (fun n hn => hS hpos' n (by omega)) (fun j => sym_le _) hpos' h0 h1 hid

/-- The share level `S5C` of step `n` from the 5-window share bound and the two ctx bounds. -/
theorem S5C_windows {T : Tables6SC} {m : Nat} (p : Snake m) (n : Nat)
    (hsh : share6 T.s [pathDir p (n+2), pathDir p (n+3), pathDir p (n+4), pathDir p (n+5),
          pathDir p (n+6), pathDir p (n+7)]
        [sym (coreAlpha p (n+3)), sym (coreAlpha p (n+4)), sym (coreAlpha p (n+5)),
          sym (coreAlpha p (n+6)), sym (coreAlpha p (n+7))] ≤
        coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) +
          coreShare 12 p (n+6) + coreShare 12 p (n+7))
    (hctx : max (ctx7A T ((win8s6 (pathDir p) n).drop 1) (syms6s6 (coreAlpha p) n))
        (ctx8A T (win8s6 (pathDir p) n) (syms6s6 (coreAlpha p) n)) ≤
      coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) + coreShare 12 p (n+6) +
        coreShare 12 p (n+7)) :
    S5C T (win8s6 (pathDir p) n) (syms6s6 (coreAlpha p) n) ≤
      coreShare 12 p (n+3) + coreShare 12 p (n+4) + coreShare 12 p (n+5) +
        coreShare 12 p (n+6) + coreShare 12 p (n+7) :=
  Nat.max_le.2 ⟨hsh, hctx⟩

/-- The bound from the certificate statements, the floor theorems and the kernel checks. -/
theorem upper_of_refuted6SC (T : Tables6SC) (keys hkeys : List (List Nat × List Nat))
    (skeys : List (List Nat × List Nat × Nat)) (ks7 ks8 : List CtxKey)
    (h : AllRefutedList keys) (hh : AllRefutedList hkeys) (hs : AllRefutedShareList skeys)
    (hs7 : AllP RefutedCtx7 ks7) (hs8 : AllP RefutedCtx8 ks8)
    (hF : Floors233)
    (hv : keysOK6 keys = true) (hc : Cover6 T.s.k6 keys)
    (hvh : keysOKH8 hkeys = true) (hch : CoverH8 T.s hkeys)
    (hcs : ShareCover T.s skeys)
    (hc7 : CtxCover 7 T.cbits (rowf7 T) ks7) (hc8 : CtxCover 8 T.cbits (rowf8 T) ks8)
    (hT : StepOK6SC T) {m : Nat} (p : Snake m) :
    (T.s.k6.num + 4200 * T.s.k6.den) * m ≤
      1099800 * T.s.k6.den + 7 * T.s.k6.num + (2 ^ T.s.k6.bits - 1) :=
  upper_of_windows6SC T hT p (direction_windows_core6S h hv hc hh hvh hch p)
    (fun hpos n hn => S5C_windows p n (share_windows6S p hF hs hcs hpos n hn)
      (ctx_windows6SC p (AllP.mem hs7) hc7 (AllP.mem hs8) hc8 hpos n hn))

theorem share6_of_zero (T : Tables6S) (hz : ∀ i t, T.shr i t = 0) (ds t : List Nat) :
    share6 T ds t = 0 := by
  have h : ∀ ds t, shareA6 T ds t = 0 := by
    intro ds t
    unfold shareA6
    cases t with
    | nil => rfl
    | cons t0 rest => simp only [shareAt6, hz, Nat.zero_shiftRight, Nat.zero_and]
  unfold share6
  rw [h, h]
  rfl

/-- The variant for a zero 5-window share table: no share keys and no floor theorems. -/
theorem upper_of_refuted6SC_noShare (T : Tables6SC) (keys hkeys : List (List Nat × List Nat))
    (ks7 ks8 : List CtxKey)
    (h : AllRefutedList keys) (hh : AllRefutedList hkeys)
    (hs7 : AllP RefutedCtx7 ks7) (hs8 : AllP RefutedCtx8 ks8)
    (hz : ∀ i t, T.s.shr i t = 0)
    (hv : keysOK6 keys = true) (hc : Cover6 T.s.k6 keys)
    (hvh : keysOKH8 hkeys = true) (hch : CoverH8 T.s hkeys)
    (hc7 : CtxCover 7 T.cbits (rowf7 T) ks7) (hc8 : CtxCover 8 T.cbits (rowf8 T) ks8)
    (hT : StepOK6SC T) {m : Nat} (p : Snake m) :
    (T.s.k6.num + 4200 * T.s.k6.den) * m ≤
      1099800 * T.s.k6.den + 7 * T.s.k6.num + (2 ^ T.s.k6.bits - 1) :=
  upper_of_windows6SC T hT p (direction_windows_core6S h hv hc hh hvh hch p)
    (fun hpos n hn => S5C_windows p n (by rw [share6_of_zero T.s hz]; exact Nat.zero_le _)
      (ctx_windows6SC p (AllP.mem hs7) hc7 (AllP.mem hs8) hc8 hpos n hn))

#print axioms upper_of_windows6SC
#print axioms upper_of_refuted6SC
#print axioms upper_of_refuted6SC_noShare
end
end Snake9
