/-
Elaboration-time numerals for the large generated tables.

`nat_lit% t` evaluates the closed term `t : Nat` with the compiled code when the definition is
elaborated and puts the resulting numeral (`Expr.lit`) into the definition.  Nothing is trusted:
the kernel only sees `def x : Nat := <numeral>`, and every property of `x` used later is proved
by the kernel.  The decoders below therefore need no proofs; they only make the source short and
the parse cheap (a decimal numeral is parsed digit by digit, quadratic in its length, and a
numeral assembled from chunks by `ofChunks` is re-assembled by the kernel at every use).

* `ofB64 s`: base-64 text, eight characters per 48-bit little-endian word
  (`A-Z a-z 0-9 + /`, least significant six bits first);
* `ofGaps s`: a sparse bit set, the gaps between consecutive set bits as base-64 varints
  (`ofGaps "..."` has bit `g1`, `g1 + g2 + 1`, ...);
* `spreadBlocks C n2 n3 m`: the `m` blocks of `n2` bytes of `C` placed `n3` bytes apart.

Uses the `Lean` meta library (part of the core distribution) for the elaborator only.
-/
import Lean

namespace Snake9.WindowAutomaton

/-- Number from little-endian words of `w` bits, combined as a balanced tree (n log n). -/
partial def ofWordsW (w : Nat) (a : Array Nat) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then a[lo]!
  else
    let mid := (lo + hi) / 2
    ofWordsW w a lo mid ||| (ofWordsW w a mid hi <<< (w * (mid - lo)))

def b64v (c : UInt8) : Nat :=
  if 65 ≤ c && c ≤ 90 then (c - 65).toNat
  else if 97 ≤ c && c ≤ 122 then (c - 71).toNat
  else if 48 ≤ c && c ≤ 57 then (c + 4).toNat
  else if c == 43 then 62 else 63

/-- Base-64 text, eight characters per 48-bit little-endian word. -/
def ofB64 (s : String) : Nat := Id.run do
  let b := s.toUTF8
  let n := b.size / 8
  let mut a : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    let mut w : Nat := 0
    for j in [0:8] do
      w := w ||| (b64v (b.get! (8 * i + j)) <<< (6 * j))
    a := a.push w
  return ofWordsW 48 a 0 n

/-- Bit set from sorted positions, balanced (cost ~ size * log(count)). -/
partial def ofBitsArr (a : Array Nat) (lo hi base : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then 1 <<< (a[lo]! - base)
  else
    let mid := (lo + hi) / 2
    let p := a[mid]!
    ofBitsArr a lo mid base ||| (ofBitsArr a mid hi p <<< (p - base))

/-- Sparse bit set: base-64 varints (five value bits per character, bit 5 = continuation) giving
the gaps `g` between set bits (next position = previous + g + 1, the first one is g). -/
def ofGaps (s : String) : Nat := Id.run do
  let b := s.toUTF8
  let mut pos : Array Nat := #[]
  let mut cur : Nat := 0
  let mut sh : Nat := 0
  let mut last : Nat := 0
  let mut first := true
  for i in [0:b.size] do
    let v := b64v (b.get! i)
    cur := cur ||| ((v % 32) <<< sh)
    if v < 32 then
      let p := if first then cur else last + cur + 1
      pos := pos.push p
      last := p; first := false; cur := 0; sh := 0
    else
      sh := sh + 5
  return ofBitsArr pos 0 pos.size 0

/-- The `m` blocks of `n2` bytes of `C`, block `h` moved to byte `n3 * h` (balanced). -/
partial def spreadBlocks (C n2 n3 lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then (C >>> (8 * n2 * lo)) &&& (2 ^ (8 * n2) - 1)
  else
    let mid := (lo + hi) / 2
    spreadBlocks C n2 n3 lo mid ||| (spreadBlocks C n2 n3 mid hi <<< (8 * n3 * (mid - lo)))

open Lean Elab Term in
/-- `nat_lit% t`: the value of the closed term `t : Nat`, computed during elaboration. -/
syntax (name := natLitElab) "nat_lit% " term : term

open Lean Elab Term in
unsafe def elabNatLitImpl : TermElab := fun stx _ => do
  let v ← evalTerm Nat (mkConst ``Nat) stx[1]
  return mkRawNatLit v

open Lean Elab Term in
@[implemented_by elabNatLitImpl]
opaque elabNatLitCore : TermElab

open Lean Elab Term in
@[term_elab natLitElab]
def elabNatLit : TermElab := elabNatLitCore

end Snake9.WindowAutomaton
