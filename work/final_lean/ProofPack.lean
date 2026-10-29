/-!
# Packed proof lists

A segment's proof is a `List Nat` of lemma words.  As a list of literals each lemma costs a
`List.cons` application and a literal object in the `.olean` (about 150 bytes) on top of its
bits.  Here many lemmas share one `Nat` literal (a chunk), decoded in the kernel.

A chunk is `n + 2^16 st`: `n` lemmas; `st` is the concatenation, lowest first, of
`len + 2^16 x` with `x < 2^(w len)`, each taking `16 + w len` bits.  No proofs are
needed: the decoded list is only data for the kernel checks, which test whatever it is.

Used by the replay modules that `gen_lean_lrat.py --packed` writes (proofs and checkpoints),
see `milestones/26-replay-efficiency/README.md`.  Keep chunks at 16 KB or less: Lean's parser
reads a long hex literal in quadratic time.
-/

namespace Snake9.ProofPack

noncomputable section

def unpackW (w : Nat) (n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih st =>
      List.cons (Nat.land (Nat.shiftRight st 16)
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul w (Nat.land st 65535))) 1))
        (ih (Nat.shiftRight st (Nat.add 16 (Nat.mul w (Nat.land st 65535)))))) n

def unpackC (w c : Nat) : List Nat := unpackW w (Nat.land c 65535) (Nat.shiftRight c 16)

/-- `xs ++ ys` by `List.rec`. -/
def app (xs ys : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) ys (fun x _ ih => List.cons x ih) xs

/-- The concatenation of the chunks `cs` (word width `w`). -/
def unpackL (w : Nat) (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => app (unpackC w x) ih) cs

end

end Snake9.ProofPack
