import WinCNF
/-!
# G1 definitions: the intended assignment of a window CNF and a clause checker

`Tables` holds decoding hints for a wincert window CNF (`ball`: vertex of each ball variable
`1..nb`; `ends`: vertex of each endpoint variable `nb+1..nb+ne`; `blocks`: the sequential
counters).  For a selection `S : Nat → Bool` of cube vertices, `tau T S` is the intended
assignment: ball variable ↦ selected, endpoint variable ↦ selected with at most one selected
neighbour, counter wire `s[i][j]` ↦ "at least `j+1` of the first `i+1` counter literals hold".

`check T c` is a Boolean recogniser of the clause shapes produced by `wincert.Encoding`; in
`W223G1Sound` it is proved that every checked clause is satisfied by `tau T S` whenever `S`
satisfies the snake facts collected in `Hyp`.  None of the tables needs to be trusted.
Core Lean only.
-/
namespace W223G1
open WinCNF

structure Block where
  base : Nat
  k : Nat
  len : Nat
  lits : List Lit
deriving Inhabited

structure Tables where
  nb : Nat
  ne : Nat
  ball : List Nat
  ends : List Nat
  window : List Nat
  blocks : List Block

/-- Cube adjacency on vertex numbers: same formula as `Snake9.Adj`. -/
def adjN (u v : Nat) : Bool := (List.range 9).any (fun k => v == Nat.xor u (2 ^ k))

/-- The nine neighbours of a vertex. -/
def nbrs (w : Nat) : List Nat := (List.range 9).map (fun k => Nat.xor w (2 ^ k))

/-- `w` is selected and has at most one selected neighbour. -/
def endSem (S : Nat → Bool) (w : Nat) : Bool :=
  S w && decide (((nbrs w).filter S).length ≤ 1)

def nBase (T : Tables) : Nat := T.nb + T.ne
def bv (T : Tables) (v : Nat) : Nat := T.ball.getD (v - 1) 0
def ev (T : Tables) (v : Nat) : Nat := T.ends.getD (v - 1 - T.nb) 0

/-- The intended values of the ball and endpoint variables. -/
def baseVal (T : Tables) (S : Nat → Bool) (v : Nat) : Bool :=
  if v = 0 then false
  else if v ≤ T.nb then S (bv T v)
  else if v ≤ nBase T then endSem S (ev T v)
  else false

/-- Number of true literals. -/
def cnt (τ : Nat → Bool) (l : List Lit) : Nat := (l.filter (litSat τ)).length

def decodeAux (v : Nat) : Nat → List Block → Option (Nat × Nat × Nat)
  | _, [] => none
  | n, b :: bs =>
    if b.base ≤ v ∧ v < b.base + b.len * b.k then some (n, (v - b.base) / b.k, (v - b.base) % b.k)
    else decodeAux v (n + 1) bs

/-- A counter wire `v` is `s[i][j]` of block `n`. -/
def wdec (T : Tables) (v : Nat) : Option (Nat × Nat × Nat) :=
  if nBase T < v then decodeAux v 0 T.blocks else none

def blk (T : Tables) (n : Nat) : Block := T.blocks.getD n default
def litAt (T : Tables) (n i : Nat) : Lit := (blk T n).lits.getD i 0

/-- The intended assignment. -/
def tau (T : Tables) (S : Nat → Bool) (v : Nat) : Bool :=
  match wdec T v with
  | some (n, i, j) => decide (j + 1 ≤ cnt (baseVal T S) ((blk T n).lits.take (i + 1)))
  | none => baseVal T S v

/-! ### The checker -/

def isBall (T : Tables) (v : Nat) : Bool := 1 ≤ v && v ≤ T.nb
def isEnd (T : Tables) (v : Nat) : Bool := T.nb < v && v ≤ nBase T
def negBall (T : Tables) : Lit → Bool
  | .negSucc n => isBall T (n + 1)
  | _ => false
def posBall (T : Tables) : Lit → Bool
  | .ofNat v => isBall T v
  | _ => false
def litV (T : Tables) (l : Lit) : Nat := bv T l.natAbs

def nodupB : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

def nbrCnt (X : List Nat) (v : Nat) : Nat := (X.filter (adjN v)).length

/-- A vertex set that is not contained in any induced path: a vertex with three neighbours in
the set, or a nonempty set in which every vertex has two neighbours (it contains a cycle). -/
def badSet (X : List Nat) : Bool :=
  X.any (fun v => decide (3 ≤ nbrCnt X v)) ||
    (!X.isEmpty && X.all (fun v => decide (2 ≤ nbrCnt X v)))

/-- Window units. -/
def ruleWindow (T : Tables) : Clause → Bool
  | [.ofNat v] => isBall T v && T.window.contains (bv T v)
  | _ => false

/-- degree ≤ 2, no 4-cycle, no 6-cycle, cycle cuts. -/
def ruleBad (T : Tables) (c : Clause) : Bool :=
  c.all (negBall T) && (nodupB (c.map (litV T)) && badSet (c.map (litV T)))

/-- interior degree ≥ 1. -/
def ruleIntDeg (T : Tables) : Clause → Bool
  | .negSucc n :: rest => isBall T (n + 1) && rest.all (posBall T) &&
      (nbrs (bv T (n + 1))).all (fun x => (rest.map (litV T)).contains x)
  | _ => false

/-- endpoint ⇒ selected. -/
def ruleEndSel (T : Tables) : Clause → Bool
  | [.negSucc e, .ofNat v] => isEnd T (e + 1) && isBall T v && ev T (e + 1) == bv T v
  | _ => false

/-- selected with at most one selected neighbour ⇒ endpoint. -/
def ruleDeg1End (T : Tables) : Clause → Bool
  | .negSucc n :: .ofNat e :: rest => isBall T (n + 1) && isEnd T e && ev T e == bv T (n + 1) &&
      rest.all (posBall T) &&
      decide (((nbrs (bv T (n + 1))).filter (fun x => !(rest.map (litV T)).contains x)).length ≤ 1)
  | _ => false

/-- endpoint ⇒ at most one selected neighbour. -/
def ruleEndDeg (T : Tables) : Clause → Bool
  | [.negSucc e, .negSucc a, .negSucc b] => isEnd T (e + 1) && isBall T (a + 1) &&
      isBall T (b + 1) && bv T (a + 1) != bv T (b + 1) &&
      (nbrs (ev T (e + 1))).contains (bv T (a + 1)) && (nbrs (ev T (e + 1))).contains (bv T (b + 1))
  | _ => false

/-- Sinz sequential-counter clauses. -/
def ruleCnt (T : Tables) : Clause → Bool
  | [.negSucc w] => match wdec T (w + 1) with
    | some (_, i, j) => i == 0 && decide (1 ≤ j)
    | none => false
  | [l, .ofNat w] =>
    (match wdec T w with
     | some (n, i, j) => j == 0 && decide (i < (blk T n).len) && l == -(litAt T n i)
     | none => false) ||
    (match l with
     | .negSucc w1 => match wdec T (w1 + 1), wdec T w with
       | some (n1, i1, j1), some (n2, i2, j2) => n1 == n2 && i2 == i1 + 1 && j1 == j2
       | _, _ => false
     | _ => false)
  | [l, .negSucc w1] => match wdec T (w1 + 1) with
    | some (n, i, j) => j + 1 == (blk T n).k && decide (i + 1 < (blk T n).len) &&
        l == -(litAt T n (i + 1))
    | none => false
  | [l, .negSucc w1, .ofNat w2] => match wdec T (w1 + 1), wdec T w2 with
    | some (n1, i1, j1), some (n2, i2, j2) => n1 == n2 && i2 == i1 + 1 && j2 == j1 + 1 &&
        decide (i2 < (blk T n2).len) && l == -(litAt T n2 i2)
    | _, _ => false
  | _ => false

def check (T : Tables) (c : Clause) : Bool :=
  ruleWindow T c || ruleBad T c || ruleIntDeg T c || ruleEndSel T c || ruleDeg1End T c ||
    ruleEndDeg T c || ruleCnt T c

/-- Well-formed counter blocks: positive width, correct length, nonzero literals over the
ball/endpoint variables. -/
def blocksOK (T : Tables) : Bool :=
  T.blocks.all (fun b => decide (1 ≤ b.k) && b.len == b.lits.length &&
    b.lits.all (fun l => l != 0 && decide (l.natAbs ≤ nBase T)))

end W223G1
