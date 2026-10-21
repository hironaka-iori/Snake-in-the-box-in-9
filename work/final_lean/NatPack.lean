/-!
# Packed lists of natural numbers

A checkpoint of a replay is a list of `2^16` clause words, about half of them `0`.  As a
Lean term each entry costs a `List.cons` application (about 100 bytes in the `.olean`),
three times its source size.  Here a list is stored as chunks, each one `Nat` literal,
and decoded in the kernel.  No proofs are needed: the decoded list is only data for the
kernel checks, which test whatever it is.

A chunk is `n + 2^8 (w + 2^16 (z + 2^n st))`: `n ≤ 255` entries, of which those with bit
`i` of the zero mask `z` set are `0`; the others are read from `st` in order, `w` bits each.
-/

namespace Snake9.NatPack

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

/-- `n` entries from the zero mask `z` and the stream `st` of `w`-bit fields (mask `m`). -/
def unpackW (w m : Nat) (n : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih z st =>
      kif Nat.beq (Nat.land z 1) 1 then List.cons 0 (ih (Nat.shiftRight z 1) st)
      else List.cons (Nat.land st m) (ih (Nat.shiftRight z 1) (Nat.shiftRight st w))) n

def unpackC (c : Nat) : List Nat :=
  let n := Nat.land c 255
  let w := Nat.land (Nat.shiftRight c 8) 65535
  let r := Nat.shiftRight c 24
  unpackW w (Nat.sub (Nat.shiftLeft 1 w) 1) n (Nat.land r (Nat.sub (Nat.shiftLeft 1 n) 1))
    (Nat.shiftRight r n)

/-- The concatenation of the chunks `cs`. -/
def unpackL (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.append (unpackC x) ih) cs

end

end Snake9.NatPack
