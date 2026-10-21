import LocalWindowTagsShare

/-!
# Packed data for share clause-soundness modules

The share analogue of `LocalWindowTagsPacked` (which stays unchanged for the existing
certificate modules).  The window meaning tree `M : MT` of a share module is decoded
by `mtB` from `LocalWindowTagsPacked`; this module adds the decoders of the share
meaning tree and of the share tag list.  `Tags.soundS` holds for any trees and tags,
so the decoders need no proofs: whatever they produce is checked by `checkAllS`.

* `mtB64 nv fuel r s st`: the share meaning tree over the variables `0 … nv`, in the
  shape of `mtB` (a node `(r, s)` splits by the next bit of the index; it is a leaf
  when `r + s > nv`), its leaves read from `st` in traversal order, 64 bits each, with
  a 2-bit type:
  - `0`: `.z`;
  - `1 + 4 (q + 2^16 a + 2^24 b)`: `.sq q a b`;
  - `2 + 4 (i + 2^10 lo + 2^26 hi + 2^42 c)`: `.t i lo hi c` (`i < 2^10`,
    `lo, hi < 2^16`, `c < 2^20`);
  - `3 + 4 (q + 2^16 t)`: `.u q t`.
* `tagsOfS n st`: `n` tags, 48 bits each: the constructor index (5 bits) and its
  arguments in fields of 8, 16 and 16 bits.  Indices `0 … 11` are the window families
  in the order of `tagOf` (wrapped in `TagS.old`), then `12` `emptyE`, `13` `totUp c`,
  `14` `totDown c`, `15` `shareCl i j`, `16` `shareCap c`.  `tagsOfSL` for long lists,
  in chunks of at most 64 tags.
* `natsOf n st`: `n` numbers of 24 bits each (totalizer literal lists).
-/

namespace Snake9.LocalWindow.Tags

noncomputable section

/-- Kernel branch `if c then t else e`, written with `Bool.rec`. -/
local macro "kif " c:term " then " t:term " else " e:term : term =>
  `(Bool.rec (motive := fun _ => _) $e $t $c)

def leafOfS (x : Nat) : MS :=
  kif Nat.beq (Nat.land x 3) 0 then MS.z else
  kif Nat.beq (Nat.land x 3) 1 then
    MS.sq (Nat.land (Nat.shiftRight x 2) 65535) (Nat.land (Nat.shiftRight x 18) 255)
      (Nat.shiftRight x 26) else
  kif Nat.beq (Nat.land x 3) 2 then
    MS.t (Nat.land (Nat.shiftRight x 2) 1023) (Nat.land (Nat.shiftRight x 12) 65535)
      (Nat.land (Nat.shiftRight x 28) 65535) (Nat.shiftRight x 44) else
    MS.u (Nat.land (Nat.shiftRight x 2) 65535) (Nat.shiftRight x 18)

/-- The share meaning tree of the index range `(r, s)` and the rest of the stream. -/
def mtB64 (nv : Nat) (fuel : Nat) : Nat → Nat → Nat → MS × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → MS × Nat) (fun _ _ st => (MS.z, st))
    (fun _ ih r s st =>
      kif Nat.ble (Nat.add r s) nv then
        (let L := ih r (Nat.add s s) st
         let R := ih (Nat.add r s) (Nat.add s s) L.2
         (MS.n L.1 R.1, R.2))
      else (leafOfS (Nat.land st 18446744073709551615), Nat.shiftRight st 64)) fuel

def tagOfS (x : Nat) : TagS :=
  let k := Nat.land x 31
  let c := Nat.land (Nat.shiftRight x 5) 255
  let i := Nat.land (Nat.shiftRight x 13) 65535
  let j := Nat.land (Nat.shiftRight x 29) 65535
  kif Nat.beq k 0 then TagS.old Tag.window else
  kif Nat.beq k 1 then TagS.old Tag.deg2 else
  kif Nat.beq k 2 then TagS.old Tag.degPos else
  kif Nat.beq k 3 then TagS.old Tag.endSel else
  kif Nat.beq k 4 then TagS.old (Tag.lowEnd c) else
  kif Nat.beq k 5 then TagS.old Tag.endLow else
  kif Nat.beq k 6 then TagS.old Tag.cut else
  kif Nat.beq k 7 then TagS.old (Tag.first c i) else
  kif Nat.beq k 8 then TagS.old (Tag.zero c j) else
  kif Nat.beq k 9 then TagS.old (Tag.mono c i j) else
  kif Nat.beq k 10 then TagS.old (Tag.step c i j) else
  kif Nat.beq k 11 then TagS.old (Tag.over c i) else
  kif Nat.beq k 12 then TagS.emptyE else
  kif Nat.beq k 13 then TagS.totUp c else
  kif Nat.beq k 14 then TagS.totDown c else
  kif Nat.beq k 15 then TagS.shareCl i j else TagS.shareCap c

def tagsOfS (n : Nat) : Nat → List TagS :=
  Nat.rec (motive := fun _ => Nat → List TagS) (fun _ => [])
    (fun _ ih st => tagOfS (Nat.land st 281474976710655) :: ih (Nat.shiftRight st 48)) n

/-- Tags from a list of chunks, each `n + 2^8 st` with `n ≤ 64` tags in `st`. -/
def tagsOfSL (cs : List Nat) : List TagS :=
  List.rec (motive := fun _ => List TagS) []
    (fun x _ ih => List.append (tagsOfS (Nat.land x 255) (Nat.shiftRight x 8)) ih) cs

/-- `n` numbers of 24 bits each. -/
def natsOf (n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih st => Nat.land st 16777215 :: ih (Nat.shiftRight st 24)) n

end

end Snake9.LocalWindow.Tags
