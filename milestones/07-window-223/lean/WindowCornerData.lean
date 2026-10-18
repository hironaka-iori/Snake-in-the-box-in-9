import Std

namespace Snake9.WindowCornerData
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Increasing coordinate pairs avoiding the two selected path directions. -/
def eligiblePairs (a b : Nat) : List (Nat × Nat) :=
  ((List.range 9).flatMap (fun c => (List.range 9).map (fun d => (c,d)))).filter
    (fun cd => decide (cd.1 < cd.2 ∧ cd.1 ≠ a ∧ cd.1 ≠ b ∧ cd.2 ≠ a ∧ cd.2 ≠ b))

def corner (v : Nat) (cd : Nat × Nat) : Nat :=
  Nat.xor (Nat.xor v (2 ^ cd.1)) (2 ^ cd.2)

def corners (v a b : Nat) : List Nat := (eligiblePairs a b).map (corner v)

theorem eligible_pairs_complete (a b c d : Nat) :
    (c,d) ∈ eligiblePairs a b ↔
      c < 9 ∧ d < 9 ∧ c < d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  simp [eligiblePairs, and_assoc]

theorem eligible_pairs_count : ∀ a b : Fin 9, a ≠ b →
    (eligiblePairs a.val b.val).length = 21 := by decide

/-- The four center/direction configurations used in the two normalized windows. -/
def configurations : List (Nat × Nat × Nat) :=
  [(1,0,1),(3,1,2),(7,2,0),(7,2,3)]

def checkedConfig (cfg : Nat × Nat × Nat) : Bool :=
  let xs := corners cfg.1 cfg.2.1 cfg.2.2
  decide (xs.length = 21 ∧ xs.Nodup ∧ ∀ x ∈ xs, x < 512)

theorem configurations_checked : configurations.all checkedConfig = true := by decide

/-- Missing events are the negations of the corner-selection indicators. -/
def missingCount (selected : Nat → Bool) (xs : List Nat) : Nat :=
  xs.countP (fun v => !(selected v))

def threshold (selected : Nat → Bool) (xs : List Nat) (j : Nat) : Bool :=
  decide (j ≤ missingCount selected xs)

def TransitionClauses (a b c s : Bool) : Prop :=
  (a = false ∨ s = true) ∧
  (b = false ∨ c = false ∨ s = true) ∧
  (s = false ∨ a = true ∨ b = true) ∧
  (s = false ∨ a = true ∨ c = true)

theorem missingCount_append (selected : Nat → Bool) (xs : List Nat) (v : Nat) :
    missingCount selected (xs ++ [v]) =
      missingCount selected xs + if selected v then 0 else 1 := by
  cases h : selected v <;> simp [missingCount, List.countP_append, h]

/-- Every positive threshold satisfies all four CNF transition clauses. -/
theorem missing_transition (selected : Nat → Bool) (xs : List Nat) (v j : Nat) :
    TransitionClauses (threshold selected xs (j+1)) (!(selected v))
      (threshold selected xs j) (threshold selected (xs ++ [v]) (j+1)) := by
  cases h : selected v <;>
    simp [TransitionClauses, threshold, missingCount_append, h] <;> omega

theorem initial_threshold (selected : Nat → Bool) (j : Nat) :
    threshold selected [] j = decide (j = 0) := by
  simp [threshold, missingCount]

theorem zeroth_threshold (selected : Nat → Bool) (xs : List Nat) :
    threshold selected xs 0 = true := by simp [threshold]

/-- The final two unit clauses express exactly the prescribed missing count. -/
theorem exact_count_clauses (selected : Nat → Bool) (xs : List Nat) (k : Nat) :
    (threshold selected xs k = true ∧ threshold selected xs (k+1) = false) ↔
      missingCount selected xs = k := by
  simp [threshold]
  omega

theorem transition_iff (a b c s : Bool) :
    TransitionClauses a b c s ↔ s = (a || (b && c)) := by
  unfold TransitionClauses
  cases a <;> cases b <;> cases c <;> cases s <;> decide

theorem missing_prefix_transition (selected : Nat → Bool) (xs : List Nat)
    (i j : Nat) (hi : i < xs.length) :
    TransitionClauses (threshold selected (xs.take i) (j+1)) (!(selected xs[i]))
      (threshold selected (xs.take i) j) (threshold selected (xs.take (i+1)) (j+1)) := by
  rw [List.take_succ_eq_append_getElem hi]
  exact missing_transition selected (xs.take i) xs[i] j

/-- The complete finite threshold-counter schema, including initial and final clauses. -/
structure MissingCounterSystem (selected : Nat → Bool) (xs : List Nat) (k : Nat)
    (s : Nat → Nat → Bool) : Prop where
  initial : ∀ j, j ≤ k+1 → s 0 j = decide (j = 0)
  zero : ∀ i, i ≤ xs.length → s i 0 = true
  step : ∀ i (hi : i < xs.length) j, j ≤ k →
    TransitionClauses (s i (j+1)) (!(selected xs[i])) (s i j) (s (i+1) (j+1))
  lower : s xs.length k = true
  upper : s xs.length (k+1) = false

theorem missing_counter_exists (selected : Nat → Bool) (xs : List Nat) (k : Nat)
    (hk : missingCount selected xs = k) :
    MissingCounterSystem selected xs k (fun i j => threshold selected (xs.take i) j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    simpa using initial_threshold selected j
  · intro i _
    exact zeroth_threshold selected (xs.take i)
  · intro i hi j _
    exact missing_prefix_transition selected xs i j hi
  · simpa using ((exact_count_clauses selected xs k).mpr hk).1
  · simpa using ((exact_count_clauses selected xs k).mpr hk).2

/-- The clauses force every represented table entry to be the actual prefix threshold. -/
theorem missing_counter_unique (selected : Nat → Bool) (xs : List Nat) (k : Nat)
    (s : Nat → Nat → Bool) (h : MissingCounterSystem selected xs k s)
    (i : Nat) (hi : i ≤ xs.length) (j : Nat) (hj : j ≤ k+1) :
    s i j = threshold selected (xs.take i) j := by
  induction i generalizing j with
  | zero => simpa [initial_threshold] using h.initial j hj
  | succ i ih =>
    cases j with
    | zero => simpa [zeroth_threshold] using h.zero (i+1) hi
    | succ j =>
      have hi' : i < xs.length := by omega
      have hs := (transition_iff _ _ _ _).mp (h.step i hi' j (by omega))
      have ht := (transition_iff _ _ _ _).mp
        (missing_prefix_transition selected xs i j hi')
      rw [ih (by omega) (j+1) hj, ih (by omega) j (by omega)] at hs
      exact hs.trans ht.symm

/-- Satisfiability of the full counter is equivalent to the intended exact cardinality. -/
theorem missing_counter_iff (selected : Nat → Bool) (xs : List Nat) (k : Nat) :
    (∃ s, MissingCounterSystem selected xs k s) ↔ missingCount selected xs = k := by
  constructor
  · rintro ⟨s,hs⟩
    have hl := hs.lower
    have hu := hs.upper
    rw [missing_counter_unique selected xs k s hs xs.length (by omega) k (by omega)] at hl
    rw [missing_counter_unique selected xs k s hs xs.length (by omega) (k+1) (by omega)] at hu
    apply (exact_count_clauses selected xs k).mp
    simpa using And.intro hl hu
  · intro hk
    exact ⟨_, missing_counter_exists selected xs k hk⟩

#print axioms eligible_pairs_complete
#print axioms eligible_pairs_count
#print axioms configurations_checked
#print axioms missing_transition
#print axioms exact_count_clauses
#print axioms missing_counter_exists
#print axioms missing_counter_unique
#print axioms missing_counter_iff
end Snake9.WindowCornerData
