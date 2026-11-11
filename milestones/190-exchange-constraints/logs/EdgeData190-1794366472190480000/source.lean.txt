import Std
namespace ExchangeAccounting190

def bit (b : Bool) : Nat := if b then 1 else 0

def edges {V : Type} (es : List (V × V)) (s : V → Bool) : Nat :=
  match es with
  | [] => 0
  | (u,v)::es => bit (s u && s v) + edges es s

def removed {V : Type} (s t : V → Bool) (v : V) : Bool := s v && !t v

def incidence {V : Type} (es : List (V × V)) (s t : V → Bool) : Nat :=
  match es with
  | [] => 0
  | (u,v)::es => (if s u && s v then bit (!t u)+bit (!t v) else 0) + incidence es s t

def boundary {V : Type} (es : List (V × V)) (s t : V → Bool) : Nat :=
  match es with
  | [] => 0
  | (u,v)::es => bit (s u && s v && (t u != t v)) + boundary es s t

theorem oneAccounting (a b c d : Bool) :
    bit (c && d) + (if a && b then bit (!c)+bit (!d) else 0) +
      bit ((c && !a) && (d && !b)) =
    bit (a && b) + (if c && d then bit (!a)+bit (!b) else 0) +
      bit ((a && !c) && (b && !d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem oneIncidence (a b c d : Bool) :
    (if a && b then bit (!c)+bit (!d) else 0) =
      2*bit ((a && !c) && (b && !d)) + bit (a && b && (c != d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

#print axioms oneAccounting
#print axioms oneIncidence
end ExchangeAccounting190
