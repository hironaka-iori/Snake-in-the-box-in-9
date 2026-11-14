import Std

/-!
Literal finite-count source prepared for kernel checking. The literal source is data/lower-dimensional-input.json,
entry "8", field "vertices". All interval visits below are recomputed from it.
The fixed coordinates are 4 and 7, packed in that order into a two-bit word.

These declarations concern finite extraction and counts. They do not prove
the full cube-model bridge, geometric clique conflict, or a search exclusion.
-/

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace ConcreteSpare47

def source : List Nat :=
  [0,1,3,7,15,13,12,28,30,62,46,38,36,52,116,124,108,109,111,103,
   119,55,183,167,175,173,172,188,184,56,40,41,43,59,187,155,153,
   137,136,138,202,194,192,193,209,211,243,227,235,233,249,253,245,
   229,228,230,238,254,250,122,106,98,96,97,113,49,177,161,160,162,
   178,50,18,82,80,88,72,73,75,91,95,223,207,205,204,220,212,214,
   150,134,132,133,149,21,85,69,68,70,78]

def base (v : Nat) : Nat :=
  (if v.testBit 4 then 1 else 0) + (if v.testBit 7 then 2 else 0)

/-- `current` is stored in reverse order. Equal consecutive base words
start a new interval; a changed base word extends the current interval. -/
def splitVisits (previous : Nat) (current : List Nat) :
    List Nat → List (List Nat)
  | [] => [current.reverse]
  | z :: zs =>
      if z = previous then
        current.reverse :: splitVisits z [z] zs
      else splitVisits z (z :: current) zs

def rawVisits : List (List Nat) :=
  match source.map base with
  | [] => []
  | z :: zs => splitVisits z [z] zs

/-- Canonical enumeration of the visited square vertices, rather than a
count of repeated index occurrences. Only genuine interval indices are used. -/
def visitSet (g : Nat) : List Nat :=
  (List.range 4).filter (fun z => decide (z ∈ rawVisits[g]!))

def multi (parity : Nat) : List Nat :=
  (List.range rawVisits.length).filter
    (fun g => decide (g % 2 = parity ∧ 1 < (visitSet g).length))

def single (parity z : Nat) : List Nat :=
  (List.range rawVisits.length).filter
    (fun g => decide (g % 2 = parity ∧ visitSet g = [z]))

def counts (parity : Nat) : List Nat :=
  [(multi parity).length, (single parity 0).length,
   (single parity 1).length, (single parity 2).length,
   (single parity 3).length]


def clique : List Nat := multi 0 ++ single 0 0 ++ single 0 2
def outside : List Nat := single 0 1 ++ single 0 3

theorem source_intervals :
    source.length = 99 ∧
    rawVisits.all (fun xs => decide (xs ≠ [] ∧ xs.Nodup)) = true := by
  decide +kernel

theorem even_counts : counts 0 = [19,7,1,5,1] := by
  decide +kernel

theorem even_partition :
    clique.length = 31 ∧ outside.length = 2 ∧
    (clique ++ outside).Nodup ∧
    (clique ++ outside).all (fun g => decide (g < rawVisits.length ∧ g % 2 = 0)) = true ∧
    (List.range rawVisits.length).all (fun g => decide (g % 2 = 0 → g ∈ clique ++ outside)) = true := by
  decide +kernel

#print axioms source_intervals
#print axioms even_counts
#print axioms even_partition
end ConcreteSpare47
