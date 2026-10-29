import LocalWindowTags

/-!
# Packed data for the core and clause-soundness modules

A window certificate has an UNSAT core `raw : List (List Nat)` (module `LocalWindowCnf.<M>`)
and, for its clause soundness, a meaning tree, a counter list and a tag list (`LocalWindowSat.<M>`,
checked by `Tags.checkAll`).  Written as list literals, the core costs about 75 bytes of
`.olean` per literal and the counters about 190 bytes per literal.  Here they are `Nat`
literals decoded in the kernel (writer: `milestones/10-window-aggregate/scripts/gen_lean_cnfsat_packed.py`):

* `unpackL lw w cs`: lists of naturals from chunks `n + 2^16 st`.  `st` holds `n` lists, lowest
  first, each a length `k` in `lw` bits followed by `k` fields of `w` bits.  The core is
  `unpackL 8 w cs`; the counters are `ctrsOf (unpackL 16 w cs)`, one list `[kind, k, lits…]`
  per counter (kind `0` is `.ends`, `1 + 2 c` is `.hi c`, `2 + 2 c` is `.lo c`).
* `mtS nv vw cw iw jw fuel 0 1 st`: a meaning tree in the shape of `Tags.mtB` (a node `(r, s)`
  splits while `r + s ≤ nv`).  Each node starts with one bit: `0` makes the whole subtree `.z`;
  after a `1` come the two subtrees, or at a leaf a 2-bit kind and its fields: `v` in `vw` bits
  for `.p v` (kind 1) and `.e v` (kind 2); `c`, `i`, `j` in `cw`, `iw`, `jw` bits for `.r c i j`
  (kind 3).  So variables that no clause or counter mentions cost one bit per pruned subtree.
* `tagsC cw iw jw n st`: `n` tags, each a 4-bit constructor index (as `Tags.tagOf`) followed
  by its arguments, `t` of `.lowEnd t` in 4 bits and `c`, `i`, `j` in `cw`, `iw`, `jw` bits;
  `tagsCL` reads chunks `n + 2^16 st`.

Every decoded number is first reduced to a numeral (`litCons`, `withLit`).  The kernel caches
its work by term, so equal numbers should be equal terms; left as `Nat.land st m` they are a
new term at every occurrence (on a 1,009-clause core: 22 s and 2.4 GB without, 18 s and
2.0 GB with, the same as the list literals).

No proofs are needed.  `Tags.sound` holds for every meaning tree, counter list and tag list
that `checkAll` accepts, and the core is only data: the clause-soundness theorem `sat` and the
replay theorem `unsat` are both about `cnf = raw.map (·.map decodeLit)`, whatever `raw`
decodes to.  A wrong decoder can only make a kernel check fail.
-/

namespace Snake9.LocalWindow.CnfPack

open Snake9.LocalWindow.Tags

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- `2^w - 1`. -/
def mask (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

/-! ## Lists of naturals (the core and the counters) -/

/-- `x :: t` with `x` first reduced to a numeral (`Nat.succ` of a literal, or `0`), so that
equal entries are equal terms: the kernel caches its work on them by term, and an entry left
as `Nat.land st m` would be a new term at every occurrence. -/
def litCons (x : Nat) (t : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (List.cons 0 t) (fun n _ => List.cons (Nat.succ n) t) x

/-- `f x` with `x` first reduced to a numeral, as in `litCons`. -/
def withLit {α : Type} (x : Nat) (f : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (f 0) (fun n _ => f (Nat.succ n)) x

/-- `k` fields of `w` bits (mask `m`) from `st`, lowest first. -/
def fields (w m : Nat) (k : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih st => litCons (Nat.land st m) (ih (Nat.shiftRight st w))) k

/-- `n` lists from `st`: a length in `lw` bits (mask `lm`), then its fields of `w` bits. -/
def lists (lw lm w m : Nat) (n : Nat) : Nat → List (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun _ ih st =>
      List.cons (fields w m (Nat.land st lm) (Nat.shiftRight st lw))
        (ih (Nat.shiftRight st (Nat.add lw (Nat.mul w (Nat.land st lm)))))) n

/-- `xs ++ ys` by `List.rec`. -/
def app (xs ys : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) ys (fun x _ ih => List.cons x ih) xs

/-- The concatenation of the lists of the chunks `cs`. -/
def unpackL (lw w : Nat) (cs : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun c _ ih => app (lists lw (mask lw) w (mask w) (Nat.land c 65535) (Nat.shiftRight c 16)) ih) cs

def kindOf (x : Nat) : Kind :=
  kif Nat.beq x 0 then Kind.ends else
  kif Nat.beq (Nat.land x 1) 1 then Kind.hi (Nat.shiftRight x 1) else
    Kind.lo (Nat.sub (Nat.shiftRight x 1) 1)

/-- The counter `[kind, k, lits…]`. -/
def ctrOf (l : List Nat) : Ctr :=
  List.rec (motive := fun _ => Ctr) dfltCtr
    (fun a t _ => List.rec (motive := fun _ => Ctr) dfltCtr (fun k lits _ => Ctr.mk lits k (kindOf a)) t) l

def ctrsOf (ls : List (List Nat)) : List Ctr :=
  List.rec (motive := fun _ => List Ctr) [] (fun l _ ih => List.cons (ctrOf l) ih) ls

/-! ## Sparse meaning trees -/

/-- The leaf at the low end of `x` and its length in bits (fields reduced to numerals). -/
def leafS (vw cw iw jw : Nat) (x : Nat) : MT × Nat :=
  kif Nat.beq (Nat.land x 3) 0 then (MT.z, 2) else
  kif Nat.beq (Nat.land x 3) 1 then
    withLit (Nat.land (Nat.shiftRight x 2) (mask vw)) (fun v => (MT.p v, Nat.add 2 vw)) else
  kif Nat.beq (Nat.land x 3) 2 then
    withLit (Nat.land (Nat.shiftRight x 2) (mask vw)) (fun v => (MT.e v, Nat.add 2 vw)) else
    withLit (Nat.land (Nat.shiftRight x 2) (mask cw)) fun c =>
    withLit (Nat.land (Nat.shiftRight x (Nat.add 2 cw)) (mask iw)) fun i =>
    withLit (Nat.land (Nat.shiftRight x (Nat.add (Nat.add 2 cw) iw)) (mask jw)) fun j =>
      (MT.r c i j, Nat.add (Nat.add (Nat.add 2 cw) iw) jw)

/-- The meaning tree of the index range `(r, s)` and the rest of the stream. -/
def mtS (nv vw cw iw jw : Nat) (fuel : Nat) : Nat → Nat → Nat → MT × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → MT × Nat) (fun _ _ st => (MT.z, st))
    (fun _ ih r s st =>
      kif Nat.beq (Nat.land st 1) 0 then (MT.z, Nat.shiftRight st 1) else
      kif Nat.ble (Nat.add r s) nv then
        (let L := ih r (Nat.add s s) (Nat.shiftRight st 1)
         let R := ih (Nat.add r s) (Nat.add s s) L.2
         (MT.n L.1 R.1, R.2))
      else
        (let x := leafS vw cw iw jw (Nat.shiftRight st 1)
         (x.1, Nat.shiftRight st (Nat.add 1 x.2)))) fuel

/-! ## Tags -/

/-- The tag at the low end of `x` and its length in bits (arguments reduced to numerals). -/
def tagC (cw iw jw : Nat) (x : Nat) : Tag × Nat :=
  let k := Nat.land x 15
  withLit (Nat.land (Nat.shiftRight x 4) 15) fun t =>
  withLit (Nat.land (Nat.shiftRight x 4) (mask cw)) fun c =>
  withLit (Nat.land (Nat.shiftRight x (Nat.add 4 cw)) (mask iw)) fun i =>
  withLit (Nat.land (Nat.shiftRight x (Nat.add 4 cw)) (mask jw)) fun j2 =>
  withLit (Nat.land (Nat.shiftRight x (Nat.add (Nat.add 4 cw) iw)) (mask jw)) fun j3 =>
  kif Nat.beq k 0 then (Tag.window, 4) else
  kif Nat.beq k 1 then (Tag.deg2, 4) else
  kif Nat.beq k 2 then (Tag.degPos, 4) else
  kif Nat.beq k 3 then (Tag.endSel, 4) else
  kif Nat.beq k 4 then (Tag.lowEnd t, 8) else
  kif Nat.beq k 5 then (Tag.endLow, 4) else
  kif Nat.beq k 6 then (Tag.cut, 4) else
  kif Nat.beq k 7 then (Tag.first c i, Nat.add (Nat.add 4 cw) iw) else
  kif Nat.beq k 8 then (Tag.zero c j2, Nat.add (Nat.add 4 cw) jw) else
  kif Nat.beq k 9 then (Tag.mono c i j3, Nat.add (Nat.add (Nat.add 4 cw) iw) jw) else
  kif Nat.beq k 10 then (Tag.step c i j3, Nat.add (Nat.add (Nat.add 4 cw) iw) jw) else
    (Tag.over c i, Nat.add (Nat.add 4 cw) iw)

/-- `n` tags from the stream `st`. -/
def tagsC (cw iw jw : Nat) (n : Nat) : Nat → List Tag :=
  Nat.rec (motive := fun _ => Nat → List Tag) (fun _ => [])
    (fun _ ih st =>
      (let t := tagC cw iw jw st
       List.cons t.1 (ih (Nat.shiftRight st t.2)))) n

/-- Tags from chunks `n + 2^16 st`. -/
def tagsCL (cw iw jw : Nat) (cs : List Nat) : List Tag :=
  List.rec (motive := fun _ => List Tag) []
    (fun x _ ih => List.append (tagsC cw iw jw (Nat.land x 65535) (Nat.shiftRight x 16)) ih) cs

end

end Snake9.LocalWindow.CnfPack
