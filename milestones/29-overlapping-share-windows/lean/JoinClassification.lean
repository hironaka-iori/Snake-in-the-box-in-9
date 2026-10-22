import Std

namespace Snake9.ShareJoin
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def canonical (ds : List Nat) : List Nat :=
  ds.map (fun d => ds.eraseDups.idxOf d)

def sameShape (ds pat : List Nat) : Bool :=
  canonical ds == pat || canonical ds.reverse == pat

def verticesFrom : Nat → List Nat → List Nat
  | v, [] => [v]
  | v, a :: ds => v :: verticesFrom (v ^^^ (1 <<< a)) ds

def induced (ds : List Nat) : Bool :=
  let vs := verticesFrom 0 ds
  decide vs.Nodup && (List.range vs.length).all (fun i =>
    (List.range vs.length).all (fun j =>
      if i+2 ≤ j then !(List.range 9).any (fun a =>
        vs.getD j 0 == (vs.getD i 0 ^^^ (1 <<< a))) else true))

def prefixTypes : List (List Nat) :=
  [[0,1,2,3,0,1], [0,1,2,3,0,4], [0,1,2,3,4,1]]

def joint (ds : List Nat) : Bool :=
  let triples := (List.range 3).map (fun i => (ds.drop i).take 6)
  canonical ds == ds && induced ds &&
    (triples.filter (fun w => sameShape w [0,1,2,3,0,4])).length == 2 &&
    (triples.filter (fun w => sameShape w [0,1,2,3,0,1])).length == 1

def candidates : List (List Nat) :=
  [[0,1,2,3,0,1,4,3], [0,1,2,3,0,4,2,3],
   [0,1,2,3,4,1,2,0], [0,1,2,3,4,1,2,5]]

/-- Exact finite classification with the normalized first six directions and
the last two coordinate names specified. This statement does not itself prove
the normalization of an arbitrary snake. -/
theorem classified : ∀ (i : Fin 3) (a b : Fin 8),
    joint (prefixTypes.getD i.val [] ++ [a.val,b.val]) = true →
    (prefixTypes.getD i.val [] ++ [a.val,b.val]) ∈ candidates := by
  decide +kernel

theorem all_candidates_pass : candidates.all joint = true := by decide +kernel

#print axioms classified
#print axioms all_candidates_pass
end Snake9.ShareJoin
