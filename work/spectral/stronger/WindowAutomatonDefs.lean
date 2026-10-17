/-
Direction-aware count automaton: definitions.

Core Lean only.  A path is read as a sequence of transition directions and a
sequence of singleton counts.  Every quantity below is computable, so the
finite step check in `WindowAutomatonData` can be evaluated by the kernel.

* `canon` relabels a direction list by order of first appearance
  (a restricted growth string).  Window exclusions and the potential table are
  keyed by canonical shapes, so they are invariant under coordinate relabelling.
* `inducedPattern` is the parity formulation of "the vertices of the segment
  are distinct and non-consecutive ones are non-adjacent": a contiguous block
  of directions must not have all multiplicities even, and a block of length at
  least two must not have exactly one odd multiplicity.
* `sym` lumps counts at least six into the symbol six (K = 5).
-/
namespace Snake9.WindowAutomaton

/-- Index of `d` in `l`, or `l.length` when absent. -/
def idx : List Nat → Nat → Nat
  | [], _ => 0
  | a :: l, d => if a = d then 0 else idx l d + 1

/-- Relabel by first appearance, given the directions seen so far. -/
def canonGo : List Nat → List Nat → List Nat
  | _, [] => []
  | seen, d :: ds => idx seen d :: canonGo (if d ∈ seen then seen else seen ++ [d]) ds

def canon (ds : List Nat) : List Nat := canonGo [] ds

/-- Distinct directions of `ds` in order of first appearance, after `seen`. -/
def seenAfter : List Nat → List Nat → List Nat
  | seen, [] => seen
  | seen, d :: ds => seenAfter (if d ∈ seen then seen else seen ++ [d]) ds

/-- Restricted growth: every label is at most the number of distinct labels before it. -/
def isRGS : List Nat → Nat → Bool
  | [], _ => true
  | a :: l, m => a ≤ m && isRGS l (if m < a + 1 then a + 1 else m)

/-- Base-8 code of a label list, with a leading sentinel digit. -/
def codeFrom : List Nat → Nat → Nat
  | [], acc => acc
  | a :: l, acc => codeFrom l (acc * 8 + a)

def shapeCode (l : List Nat) : Nat := codeFrom l 1

/-- Counts above six are lumped. -/
def sym (a : Nat) : Nat := if a ≤ 6 then a else 6

/-- Base-7 index of a symbol list (symbols are 1..6, so digits 1..6 of base 7). -/
def symIdx : List Nat → Nat → Nat
  | [], acc => acc
  | s :: l, acc => symIdx l (acc * 7 + s)

/-! ### Parity-based induced-path test on direction blocks -/

/-- Distinct elements of `l`, in order of first appearance. -/
def firsts : List Nat → List Nat → List Nat
  | seen, [] => seen.reverse
  | seen, d :: ds => firsts (if d ∈ seen then seen else d :: seen) ds

/-- Number of distinct directions occurring an odd number of times. -/
def oddCount (seg : List Nat) : Nat :=
  ((firsts [] seg).filter (fun d => seg.count d % 2 == 1)).length

/-- A block is admissible when its vertices are distinct (not all even) and,
if it has at least two steps, its ends are not adjacent (not exactly one odd). -/
def blockOK (seg : List Nat) : Bool :=
  oddCount seg != 0 && (seg.length < 2 || oddCount seg != 1)

/-- Nonempty prefixes of `l` of length at most `n`. -/
def prefixes : List Nat → List (List Nat)
  | [] => []
  | a :: l => [a] :: (prefixes l).map (a :: ·)

/-- All contiguous nonempty blocks. -/
def blocks : List Nat → List (List Nat)
  | [] => []
  | a :: l => prefixes (a :: l) ++ blocks l

def inducedPattern (ds : List Nat) : Bool := (blocks ds).all blockOK

/-! ### Enumeration helpers -/

def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

/-- All restricted growth strings of length `n` continuing a prefix with bound `m`. -/
def allRGS : Nat → Nat → (List Nat → Bool) → Bool
  | 0, _, p => p []
  | n + 1, m, p => allBelow (m + 1) (fun a => allRGS n (if m < a + 1 then a + 1 else m) (fun l => p (a :: l)))

/-- All symbols 1..6. -/
def allSym (p : Nat → Bool) : Bool := allBelow 6 (fun s => p (s + 1))

theorem allBelow_spec : ∀ n (p : Nat → Bool), allBelow n p = true → ∀ a, a < n → p a = true
  | 0, _, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | n + 1, p, h, a, ha => by
    simp only [allBelow, Bool.and_eq_true] at h
    by_cases hn : a = n
    · subst hn; exact h.2
    · exact allBelow_spec n p h.1 a (by omega)

theorem allSym_spec (p : Nat → Bool) (h : allSym p = true) (s : Nat) (h1 : 1 ≤ s) (h6 : s ≤ 6) :
    p s = true := by
  have := allBelow_spec 6 _ h (s - 1) (by omega)
  simpa [show s - 1 + 1 = s by omega] using this

theorem allRGS_spec : ∀ n m (p : List Nat → Bool), allRGS n m p = true →
    ∀ l, l.length = n → isRGS l m = true → p l = true
  | 0, m, p, h, [], _, _ => h
  | 0, m, p, h, _ :: _, hl, _ => by simp at hl
  | n + 1, m, p, h, [], hl, _ => by simp at hl
  | n + 1, m, p, h, a :: l, hl, hr => by
    simp only [isRGS, Bool.and_eq_true, decide_eq_true_eq] at hr
    have ha := allBelow_spec (m + 1) _ h a (by omega)
    exact allRGS_spec n _ _ ha l (by simpa using hl) hr.2

end Snake9.WindowAutomaton
