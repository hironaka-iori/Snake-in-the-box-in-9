import Std

namespace CubeCut237

def axes : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256]

def bit (v : Nat) : Nat := 1 <<< v

/-- Bit set of the nine neighbours of a vertex in the labelled cube. -/
def neighbours (z : Nat) : Nat :=
  axes.foldl (fun mask i => mask ||| bit (z ^^^ i)) 0

/-- Each unordered axis pair gives one vertex at distance two from u.
The two cube vertices between them are its only possible labels. -/
def escapes (selected inside u : Nat) : Nat :=
  (axes.map fun i =>
    (axes.filter fun j =>
      let w := (u ^^^ i) ^^^ j
      let pair := bit u ||| bit w
      i < j && (selected &&& bit w) != 0 && (inside &&& bit w) == 0 &&
        ((selected &&& neighbours (u ^^^ i)) == pair ||
         (selected &&& neighbours (u ^^^ j)) == pair)).length).sum

def encode (vs : List Nat) : Nat := vs.foldl (fun m v => m ||| bit v) 0

def violated (selected : Nat) (s t : List Nat) : Bool :=
  let inside := encode t
  s.all (fun u => u < 512 && (bit u &&& selected) != 0) &&
  t.all (fun u => u < 512 && (bit u &&& selected) != 0) &&
  s.eraseDups.length == s.length && t.eraseDups.length == t.length &&
  decide (2*t.length + 2 + (s.map (escapes selected inside)).sum < 2*s.length)

end CubeCut237
