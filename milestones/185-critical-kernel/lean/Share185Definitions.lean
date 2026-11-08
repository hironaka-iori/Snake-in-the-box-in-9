import LocalWindowTags
import LocalWindowShareModel

/-!
# Clause soundness for share certificates

Stage 2 of `milestones/11-local-ceiling/s0_lean_design.md` (§4.2).  A share certificate
refutes a CNF that adds to the window clauses of `LocalWindowTags` the corner-share
clauses of `milestones/11-local-ceiling/s0_radius4/e1lib.py` (`ShareModel`) with a
static cap.  This module extends the clause-soundness checker to these clauses without
touching `MT`, `Tag`, `tau`, `checkAll` or `sound` (which the existing certificate
modules use):

* `M : MT` keeps the meanings of the window variables (`.p`, `.e`, `.r`).  A second
  tree `X : MS` gives the meanings of the share variables, read only where `M` has no
  window meaning:
  - `.sq q a b`: the square at `q` spanned by `a, b` is empty (`emptyPred S q (a, b)`);
  - `.u q t`: `t ≤ ⌊Mr · e0(q) / d(q)⌋` (`fl Mr S q`);
  - `.t i lo hi c`: at least `c` literals of the block `[lo, hi)` of totalizer `i` hold.
* `tots : List Tot` lists the totalizers, each with the reason why its count is
  bounded (`TotKind`): the empty squares at `q`, the neighbours of `q`, or the cap
  totalizer over the threshold variables of the window's share neighbours.
* `TagS` names the clause family: an old family (`old t`, checked by `ckClause` after
  checking that every literal is a window variable), or one of the five share families
  `emptyE`, `totUp`, `totDown`, `shareCl`, `shareCap`.

`soundS`: a checked certificate gives, from any `S`, `E` with `AxiomsS`, an assignment
`tauS` satisfying every core clause; `refutedShare_of_sat` turns this and a refutation
of the core into `RefutedShare`.

Departures from the design note: the share data `ShareQ` of §4.2 is replaced by the
totalizer kinds (`TotKind.emp q`, `.nb q`, `.cap spec`), checked once per totalizer by
`totOK`; `shareCl` carries the two totalizer indices only (the threshold `dd` is read
off the literal of the neighbour totalizer); the empty-square literals of `.emp q` need
only form a sublist of the 36 pairs, so the checker does not need the direction `kk`.
-/

namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags

open Snake9.LocalWindow

/-! ## Data -/

/-- Meanings of the share variables, and binary trees of them. -/
inductive MS where
  | z
  | sq (q a b : Nat)
  | t (i lo hi c : Nat)
  | u (q t : Nat)
  | n (lt rt : MS)

def MS.get : MS → Nat → MS
  | .n lt rt, x => if x % 2 = 0 then lt.get (x / 2) else rt.get (x / 2)
  | .z, _ => .z
  | .sq q a b, _ => .sq q a b
  | .t i lo hi c, _ => .t i lo hi c
  | .u q tt, _ => .u q tt

/-- Why the count of a totalizer is bounded. -/
inductive TotKind where
  /-- Positive empty-square literals at `q`: at most `e0(q)` hold. -/
  | emp (q : Nat)
  /-- The primaries of `nbrs q`, in order: exactly `d(q)` hold. -/
  | nb (q : Nat)
  /-- Positive threshold literals `u q t`, per centre the neighbours `q = c ⊕ e_kk`
  listed in `spec` as `(kk, tmax)` with `t = 1 … tmax`: at most `shareSum` hold. -/
  | cap (spec : List (List (Nat × Nat)))

/-- A totalizer: its input literals and its kind. -/
structure Tot where
  lits : List Nat
  kind : TotKind

def dfltTot : Tot := ⟨[], .cap []⟩

/-- Clause families of a share CNF. -/
inductive TagS where
  /-- A window clause family of `LocalWindowTags`. -/
  | old (t : Tag)
  /-- `[X q, X q^a, X q^b, X q^ab, E]`. -/
  | emptyE
  /-- `[o] ++ opt [-a] ++ opt [-b]` in totalizer `i`. -/
  | totUp (i : Nat)
  /-- `[-o] ++ opt [a] ++ opt [b]` in totalizer `i`. -/
  | totDown (i : Nat)
  /-- `[u] ++ [-ge] ++ opt [gd]`, `ge` in totalizer `eT`, `gd` in totalizer `dT`. -/
  | shareCl (eT dT : Nat)
  /-- `[-o]`, `o` an output above the cap of the cap totalizer `i`. -/
  | shareCap (i : Nat)

/-! ## The assignment -/

/-- `⌊Mr · e0(q) / d(q)⌋`, the share `q` gives to each selected neighbour. -/
def fl (Mr : Nat) (S : Nat → Bool) (q : Nat) : Nat := Mr * emptyCount S q / cnt S (nbrs q)

/-- `x` is a window variable. -/
def oldVar (M : MT) (x : Nat) : Bool :=
  match M.get x with
  | .p _ => true
  | .e _ => true
  | .r _ _ _ => true
  | _ => false

/-- Values of the square and threshold variables. -/
def sval (S : Nat → Bool) (Mr : Nat) (X : MS) (x : Nat) : Bool :=
  match X.get x with
  | .sq q a b => emptyPred S q (a, b)
  | .u q t => decide (t ≤ fl Mr S q)
  | _ => false

/-- Values of the totalizer inputs. -/
def baseS (S E : Nat → Bool) (M : MT) (X : MS) (Mr : Nat) (x : Nat) : Bool :=
  if oldVar M x then base S E M x else sval S Mr X x

/-- The block `[lo, hi)` of a list. -/
def blk (l : List Nat) (lo hi : Nat) : List Nat := (l.drop lo).take (hi - lo)

/-- Number of true literals in the block `[lo, hi)` of totalizer `i`. -/
def bc (S E : Nat → Bool) (M : MT) (X : MS) (Mr : Nat) (tots : List Tot) (i lo hi : Nat) : Nat :=
  (blk (tots.getD i dfltTot).lits lo hi).countP (lv (baseS S E M X Mr))

def tauS (S E : Nat → Bool) (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot)
    (x : Nat) : Bool :=
  if oldVar M x then tau S E M cs x else
  match X.get x with
  | .t i lo hi c => decide (c ≤ bc S E M X Mr tots i lo hi)
  | _ => sval S Mr X x

/-! ## The checker -/

/-- A positive literal over a share variable. -/
def posS (M : MT) (a : Nat) : Bool := a % 2 == 0 && decide (2 ≤ a) && !oldVar M (a / 2)

def sqOf (X : MS) (a : Nat) : Option (Nat × Nat × Nat) :=
  match X.get (a / 2) with
  | .sq q a b => some (q, a, b)
  | _ => none

def uOf (X : MS) (a : Nat) : Option (Nat × Nat) :=
  match X.get (a / 2) with
  | .u q t => some (q, t)
  | _ => none

/-- Square vertex and pair of a literal (`(0, 0, 0)` if it is not a square literal). -/
def sqQ (X : MS) (a : Nat) : Nat := ((sqOf X a).getD (0, 0, 0)).1
def sqAB (X : MS) (a : Nat) : Nat × Nat := ((sqOf X a).getD (0, 0, 0)).2
def uQT (X : MS) (a : Nat) : Nat × Nat := (uOf X a).getD (0, 0)

def isSq (X : MS) (a : Nat) : Bool := (sqOf X a).isSome
def isU (X : MS) (a : Nat) : Bool := (uOf X a).isSome

def posSq (M : MT) (X : MS) (a : Nat) : Bool := posS M a && isSq X a
def posU (M : MT) (X : MS) (a : Nat) : Bool := posS M a && isU X a

/-- A literal over a primary, an endpoint flag, a square or a threshold variable. -/
def baseOKS (M : MT) (X : MS) (l : Nat) : Bool :=
  decide (2 ≤ l) &&
    if oldVar M (l / 2) then isP M (l / 2) || isE M (l / 2) else isSq X l || isU X l

/-- The block meaning of a positive totalizer literal of totalizer `i`. -/
def tInfo (M : MT) (X : MS) (i a : Nat) : Option (Nat × Nat × Nat) :=
  if posS M a then
    match X.get (a / 2) with
    | .t i' lo hi c => if i' = i then some (lo, hi, c) else none
    | _ => none
  else none

/-- The block meaning `(lo, hi, c)` of a literal of totalizer `i`: a totalizer output,
or the input literal at position `pos` itself (a leaf, block `[pos, pos+1)`, `c = 1`). -/
def litInfo (M : MT) (X : MS) (tots : List Tot) (i a pos : Nat) : Option (Nat × Nat × Nat) :=
  match tInfo M X i a with
  | some r => some r
  | none =>
    if a = (tots.getD i dfltTot).lits.getD pos 0 ∧ pos < (tots.getD i dfltTot).lits.length then
      some (pos, pos + 1, 1) else none

/-- The negation of a literal code. -/
def negL (x : Nat) : Nat := if x % 2 = 0 then x + 1 else x - 1

/-- Greedy sublist test. -/
def sublG {α : Type} [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then sublG as bs else sublG (a :: as) bs

/-- The threshold literals of the cap totalizer, per centre and neighbour. -/
def capL : List Centre → List (List (Nat × Nat)) → List (Nat × Nat)
  | c :: cs, s :: ss =>
    (s.flatMap fun kt => (List.range kt.2).map fun t => (c.v ^^^ (1 <<< kt.1), t + 1)) ++ capL cs ss
  | _, _ => []

def totOK (M : MT) (X : MS) (w : List Nat) (cens : List Centre) (t : Tot) : Bool :=
  t.lits.all (baseOKS M X) &&
  match t.kind with
  | .emp q => t.lits.all (fun a => posSq M X a && sqQ X a == q) &&
      sublG (t.lits.map (sqAB X)) (freePairs 9 9)
  | .nb q => t.lits.all (posP M) && t.lits.map (vl M) == nbrs q &&
      (nbrs q).any (fun v => w.contains v)
  | .cap spec => t.lits.all (posU M X) && (t.lits.map (uQT X)).isPerm (capL cens spec) &&
      spec.all (fun s => subl (s.map (·.1)) (List.range 9))

def isEmp (q : Nat) : TotKind → Bool
  | .emp q' => q' == q
  | _ => false

def isNb (q : Nat) : TotKind → Bool
  | .nb q' => q' == q
  | _ => false

def isCap : TotKind → Bool
  | .cap _ => true
  | _ => false

def oldLits (M : MT) (cl : List Nat) : Bool := cl.all fun a => decide (2 ≤ a) && oldVar M (a / 2)

def ckEmptyE (M : MT) (X : MS) : List Nat → Bool
  | [a1, a2, a3, a4, e] => posP M a1 && posP M a2 && posP M a3 && posP M a4 && posSq M X e &&
      vl M a1 == sqQ X e && vl M a2 == sqQ X e ^^^ (1 <<< (sqAB X e).1) &&
      vl M a3 == sqQ X e ^^^ (1 <<< (sqAB X e).2) &&
      vl M a4 == sqQ X e ^^^ (1 <<< (sqAB X e).1) ^^^ (1 <<< (sqAB X e).2)
  | _ => false

def subUp (lo hi c : Nat) : Option (Nat × Nat × Nat) → Bool
  | some (l, h, c1) => decide (lo ≤ l ∧ l ≤ h ∧ h ≤ hi ∧ c ≤ c1)
  | none => false

def subDown (lo hi c : Nat) : Option (Nat × Nat × Nat) → Bool
  | some (l, h, c1) => decide (lo ≤ l ∧ l ≤ h ∧ h ≤ hi ∧ l - lo + c1 + (hi - h) ≤ c)
  | none => false

def twoUp (lo hi c : Nat) : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Bool
  | some (l1, h1, c1), some (l2, h2, c2) =>
    decide (lo ≤ l1 ∧ l1 ≤ h1 ∧ h1 ≤ l2 ∧ l2 ≤ h2 ∧ h2 ≤ hi ∧ c ≤ c1 + c2)
  | _, _ => false

def twoDown (lo hi c : Nat) : Option (Nat × Nat × Nat) → Option (Nat × Nat × Nat) → Bool
  | some (l1, h1, c1), some (l2, h2, c2) =>
    decide (lo ≤ l1 ∧ l1 ≤ h1 ∧ h1 ≤ l2 ∧ l2 ≤ h2 ∧ h2 ≤ hi ∧
      l1 - lo + c1 + (l2 - h1) + c2 + (hi - h2) ≤ c + 1)
  | _, _ => false

def ckTotUp (M : MT) (X : MS) (tots : List Tot) (i : Nat) : List Nat → Bool
  | [o, x] => decide (2 ≤ x) &&
    match tInfo M X i o with
    | some (lo, hi, c) => subUp lo hi c (litInfo M X tots i (negL x) lo) ||
        subUp lo hi c (litInfo M X tots i (negL x) (hi - 1))
    | none => false
  | [o, x, y] => decide (2 ≤ x) && decide (2 ≤ y) &&
    match tInfo M X i o with
    | some (lo, hi, c) =>
      twoUp lo hi c (litInfo M X tots i (negL x) lo) (litInfo M X tots i (negL y) (hi - 1))
    | none => false
  | _ => false

def ckTotDown (M : MT) (X : MS) (tots : List Tot) (i : Nat) : List Nat → Bool
  | [o, x] => decide (2 ≤ o) && decide (2 ≤ x) &&
    match tInfo M X i (negL o) with
    | some (lo, hi, c) => subDown lo hi c (litInfo M X tots i x lo) ||
        subDown lo hi c (litInfo M X tots i x (hi - 1))
    | none => false
  | [o, x, y] => decide (2 ≤ o) && decide (2 ≤ x) && decide (2 ≤ y) &&
    match tInfo M X i (negL o) with
    | some (lo, hi, c) =>
      twoDown lo hi c (litInfo M X tots i x lo) (litInfo M X tots i y (hi - 1))
    | none => false
  | _ => false

def ckShareCl (M : MT) (X : MS) (Mr : Nat) (tots : List Tot) (eT dT : Nat) : List Nat → Bool
  | [u, x] => decide (2 ≤ x) && posU M X u &&
    isEmp (uQT X u).1 (tots.getD eT dfltTot).kind &&
    isNb (uQT X u).1 (tots.getD dT dfltTot).kind &&
    match litInfo M X tots eT (negL x) 0 with
    | some (_, _, cn) => decide ((uQT X u).2 * 9 ≤ Mr * cn)
    | none => false
  | [u, x, y] => decide (2 ≤ x) && decide (2 ≤ y) && posU M X u &&
    isEmp (uQT X u).1 (tots.getD eT dfltTot).kind &&
    isNb (uQT X u).1 (tots.getD dT dfltTot).kind &&
    match litInfo M X tots eT (negL x) 0, litInfo M X tots dT y 0 with
    | some (_, _, cn), some (l, h, c2) =>
      decide (l = 0 ∧ 9 ≤ h ∧ (uQT X u).2 * (c2 - 1) ≤ Mr * cn)
    | _, _ => false
  | _ => false

def ckShareCap (M : MT) (X : MS) (tots : List Tot) (cap i : Nat) : List Nat → Bool
  | [x] => decide (2 ≤ x) && isCap (tots.getD i dfltTot).kind &&
    match tInfo M X i (negL x) with
    | some (_, _, c) => decide (cap + 1 ≤ c)
    | none => false
  | _ => false

def ckClauseS (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (cap : Nat) : TagS → List Nat → Bool
  | .old t, cl => oldLits M cl && ckClause M cs w t cl
  | .emptyE, cl => ckEmptyE M X cl
  | .totUp i, cl => ckTotUp M X tots i cl
  | .totDown i, cl => ckTotDown M X tots i cl
  | .shareCl eT dT, cl => ckShareCl M X Mr tots eT dT cl
  | .shareCap i, cl => ckShareCap M X tots cap i cl

def ckAllS (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (cap : Nat) : List TagS → List (List Nat) → Bool
  | [], [] => true
  | t :: ts, cl :: cls => ckClauseS M X Mr cs tots w cap t cl && ckAllS M X Mr cs tots w cap ts cls
  | _, _ => false

/-- The share checker: counters, totalizers, and one tag per core clause. -/
def checkAllS (M : MT) (X : MS) (Mr : Nat) (cs : List Ctr) (tots : List Tot) (w : List Nat)
    (b : List (Nat × Nat)) (cap : Nat) (tags : List TagS) (raw : List (List Nat)) : Bool :=
  cs.all (ctrOK M (centresK w b)) && tots.all (totOK M X w (centresK w b)) &&
    ckAllS M X Mr cs tots w cap tags raw


end Snake9.LocalWindow.Tags185
