import CountWindowPairs231

/-! A finite coverage interface for every length of the actual 231 count table.
Concrete table checks and local refutations remain separate obligations.
-/
namespace Snake9.CountWindowTable231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
set_option maxHeartbeats 1000000

def allPositiveSyms (K : Nat) : Nat → (List Nat → Bool) → Bool
  | 0, f => f []
  | n + 1, f => allBelow K (fun s => allPositiveSyms K n (fun l => f ((s+1) :: l)))

theorem allPositiveSyms_spec (K : Nat) : ∀ n (f : List Nat → Bool),
    allPositiveSyms K n f = true → ∀ l : List Nat, l.length = n →
    (∀ s ∈ l, 1 ≤ s ∧ s ≤ K) → f l = true
  | 0, _, h, [], _, _ => h
  | 0, _, _, _ :: _, hl, _ => by simp at hl
  | _ + 1, _, _, [], hl, _ => by simp at hl
  | n + 1, f, h, s :: l, hl, hs => by
    have hhead := hs s List.mem_cons_self
    have h1 := allBelow_spec K _ h (s-1) (by omega)
    rw [show s - 1 + 1 = s by omega] at h1
    exact allPositiveSyms_spec K n _ h1 l (by simpa using hl)
      (fun x hx => hs x (List.mem_cons_of_mem _ hx))

def covered (keys : List IntervalKey) (ds syms : List Nat) : Bool :=
  !wforbK6R34C7W ds syms || intervalHit 8 keys ds syms ||
    intervalHit 8 keys ds.reverse syms.reverse

def shapeCovered (keys : List IntervalKey) (ds : List Nat) : Bool :=
  !inducedPattern ds || allPositiveSyms 8 (ds.length - 1) (covered keys ds)

def tableCovered (keys : List IntervalKey) (n : Nat) : Bool :=
  allRGS n 0 (shapeCovered keys)

theorem canon_idem (ds : List Nat) : canon (canon ds) = canon ds := by
  simpa using canon_canon_drop ds 0

theorem canon_reverse (ds : List Nat) : canon (canon ds).reverse = canon ds.reverse := by
  simpa using canon_canon_drop_reverse ds 0

theorem covered_canon (keys : List IntervalKey) (ds syms : List Nat) :
    covered keys (canon ds) syms = covered keys ds syms := by
  simp only [covered, wforbK6R34C7W, wshK6R34C7W, intervalHit,
    canon_idem, canon_reverse]

theorem symsK_positive {m : Nat} (p : Snake m) (K r n : Nat)
    (hK : 1 ≤ K) (hr : r + n ≤ m) :
    ∀ s ∈ symsK p K r n, 1 ≤ s ∧ s ≤ K := by
  intro s hs
  simp only [symsK, List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact ⟨symK_ge_one K _ hK (CountWindowPairs231.coreAlpha_pos p (r+i+1) (by omega)),
    symK_le_K _ _⟩

/-- Table coverage and a proved interval family together discharge the actual
packed-table predicate on any snake window of this length. -/
theorem no_window {keys : List IntervalKey} {n : Nat}
    (hc : tableCovered keys n = true) (hf : AllRefutedIntervals keys)
    {m : Nat} (p : Snake m) (r : Nat) (hn : 1 ≤ n) (hr : r + n ≤ m) :
    wforbK6R34C7W (dsOf p r n) (symsK p 8 r n) = false := by
  have hshape := allRGS_spec n 0 _ hc (canon (dsOf p r n))
    (by simp [length_canon, dsOf]) (canon_isRGS _)
  have hind : inducedPattern (canon (dsOf p r n)) = true := by
    rw [inducedPattern_canon, ← ParallelShareShapeBridge.blockList_eq_dsOf p r n hr]
    exact snake_inducedPattern_block p r n hr
  simp only [shapeCovered, hind, Bool.not_true, Bool.false_or] at hshape
  have hcover := allPositiveSyms_spec 8 _ _ hshape (symsK p 8 r n)
    (by simp [symsK_length, length_canon, dsOf]) (symsK_positive p 8 r n (by decide) hr)
  rw [covered_canon] at hcover
  simp only [covered, no_interval_hit hf p r n hn hr,
    no_reverse_interval_hit hf p r n hn hr, Bool.or_false] at hcover
  simpa using hcover

#print axioms allPositiveSyms_spec
#print axioms covered_canon
#print axioms no_window
end Snake9.CountWindowTable231
