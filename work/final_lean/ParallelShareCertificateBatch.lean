import ParallelShareCertificate

/-! Binary meaning lookup and checked concatenation of clause shards. -/
namespace Snake9.ParallelShareCertificate
open Snake9.LocalWindow Snake9.ParallelShareBlocks Snake9.ParallelShareClauses

inductive MeaningTree where
  | leaf (value : Option Meaning)
  | node (left right : MeaningTree)

def MeaningTree.get : MeaningTree → Nat → Option Meaning
  | .leaf value, _ => value
  | .node left right, x => if x % 2 = 0 then left.get (x / 2) else right.get (x / 2)

theorem checkRaw_append (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat)
    (ts : List Term) (M : Nat → Option Meaning) (cap : Nat) :
    ∀ (tags1 : List Tag) (raw1 : List (List Nat)),
      checkRaw oldM ctrs w ts M cap tags1 raw1 = true →
      ∀ (tags2 : List Tag) (raw2 : List (List Nat)),
        checkRaw oldM ctrs w ts M cap tags2 raw2 = true →
        checkRaw oldM ctrs w ts M cap (tags1 ++ tags2) (raw1 ++ raw2) = true
  | [], [], _, _, _, h2 => h2
  | t :: tags, c :: raw, h1, tags2, raw2, h2 => by
    simp only [checkRaw, Bool.and_eq_true] at h1
    simp only [List.cons_append, checkRaw, h1.1, Bool.true_and]
    exact checkRaw_append oldM ctrs w ts M cap tags raw h1.2 tags2 raw2 h2
  | [], _ :: _, h, _, _, _ => by simp [checkRaw] at h
  | _ :: _, [], h, _, _, _ => by simp [checkRaw] at h

theorem checkRaw_flatMap (oldM : Tags.MT) (ctrs : List Tags.Ctr) (w : List Nat)
    (ts : List Term) (M : Nat → Option Meaning) (cap : Nat)
    (parts : List (List Tag × List (List Nat)))
    (h : ∀ p ∈ parts, checkRaw oldM ctrs w ts M cap p.1 p.2 = true) :
    checkRaw oldM ctrs w ts M cap (parts.flatMap Prod.fst) (parts.flatMap Prod.snd) = true := by
  induction parts with
  | nil => rfl
  | cons p parts ih =>
    exact checkRaw_append oldM ctrs w ts M cap p.1 p.2 (h p (by simp)) _ _
      (ih (fun q hq => h q (by simp [hq])))

#print axioms checkRaw_flatMap
end Snake9.ParallelShareCertificate
