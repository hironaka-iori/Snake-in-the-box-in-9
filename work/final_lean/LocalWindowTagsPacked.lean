import LocalWindowTags

/-!
# Packed data for the clause-soundness modules

A clause-soundness module `LocalWindowSat.<M>` gives a meaning tree, counters and a tag
list to `Tags.checkAll`.  Written as Lean terms, the meaning tree (thousands of nested
constructors) and the tag list took most of the module's build time to elaborate.  Here
they are single `Nat` literals decoded in the kernel.  The soundness theorem
`Tags.sound` holds for any meaning tree and tag list, so the decoders need no proofs:
whatever they produce is checked by `checkAll`.

* `mtB nv fuel r s st`: the meaning tree over the variables `0 … nv` in the shape of
  `gen_lean_sat.lean_tree_terms` (a node `(r, s)` splits by the next bit of the index;
  it is a leaf when `r + s > nv`), its leaves read from `st` in traversal order, 48 bits
  each: `0` for `.z`, `1 + 4 v` for `.p v`, `2 + 4 v` for `.e v`,
  `3 + 4 (c + 2^8 i + 2^24 j)` for `.r c i j`.
* `tagsOf n st`: `n` tags, 48 bits each: the constructor index (4 bits) and its
  arguments in fields of 8, 16 and 16 bits.
-/

namespace Snake9.LocalWindow.Tags

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

def leafOf (x : Nat) : MT :=
  kif Nat.beq (Nat.land x 3) 0 then MT.z else
  kif Nat.beq (Nat.land x 3) 1 then MT.p (Nat.shiftRight x 2) else
  kif Nat.beq (Nat.land x 3) 2 then MT.e (Nat.shiftRight x 2) else
    MT.r (Nat.land (Nat.shiftRight x 2) 255) (Nat.land (Nat.shiftRight x 10) 65535)
      (Nat.shiftRight x 26)

/-- The meaning tree of the index range `(r, s)` and the rest of the stream. -/
def mtB (nv : Nat) (fuel : Nat) : Nat → Nat → Nat → MT × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → MT × Nat) (fun _ _ st => (MT.z, st))
    (fun _ ih r s st =>
      kif Nat.ble (Nat.add r s) nv then
        (let L := ih r (Nat.add s s) st
         let R := ih (Nat.add r s) (Nat.add s s) L.2
         (MT.n L.1 R.1, R.2))
      else (leafOf (Nat.land st 281474976710655), Nat.shiftRight st 48)) fuel

def tagOf (x : Nat) : Tag :=
  let k := Nat.land x 15
  let c := Nat.land (Nat.shiftRight x 4) 255
  let i := Nat.land (Nat.shiftRight x 12) 65535
  let j := Nat.land (Nat.shiftRight x 28) 65535
  kif Nat.beq k 0 then Tag.window else
  kif Nat.beq k 1 then Tag.deg2 else
  kif Nat.beq k 2 then Tag.degPos else
  kif Nat.beq k 3 then Tag.endSel else
  kif Nat.beq k 4 then Tag.lowEnd c else
  kif Nat.beq k 5 then Tag.endLow else
  kif Nat.beq k 6 then Tag.cut else
  kif Nat.beq k 7 then Tag.first c i else
  kif Nat.beq k 8 then Tag.zero c j else
  kif Nat.beq k 9 then Tag.mono c i j else
  kif Nat.beq k 10 then Tag.step c i j else Tag.over c i

def tagsOf (n : Nat) : Nat → List Tag :=
  Nat.rec (motive := fun _ => Nat → List Tag) (fun _ => [])
    (fun _ ih st => tagOf (Nat.land st 281474976710655) :: ih (Nat.shiftRight st 48)) n

end

end Snake9.LocalWindow.Tags
