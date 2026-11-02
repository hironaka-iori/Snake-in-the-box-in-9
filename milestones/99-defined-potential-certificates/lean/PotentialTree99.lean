import BalancedLookup

namespace Snake9.Potential99

/-- Six consecutive subintervals share a node whenever their data agree. -/
inductive Tree where
  | leaf (n : Nat)
  | node (width : Nat) (a b c d e f : Tree)

def value : Tree → Nat → Nat
  | .leaf n, _ => n
  | .node w a b c d e f, i =>
      if i < w then value a i
      else if i < 2*w then value b (i-w)
      else if i < 3*w then value c (i-2*w)
      else if i < 4*w then value d (i-3*w)
      else if i < 5*w then value e (i-4*w)
      else value f (i-5*w)

end Snake9.Potential99
