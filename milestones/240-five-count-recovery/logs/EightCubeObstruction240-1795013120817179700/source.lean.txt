import Std
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace EightCubeObstruction240

-- These are eight literal even vertices of Q9. This file checks a matrix
-- obstruction only, not a counterexample to binary-selection recovery.
def points : List Nat := [0, 510, 509, 3, 507, 5, 6, 504]
def signs : List Int := [1, -1, -1, 1, -1, 1, 1, -1]
def point (i : Nat) : Nat := points.getD i 0
def chi (i : Nat) : Int := signs.getD i 0

def popcount9 (x : Nat) : Nat :=
  ((List.range 9).map (fun k => if Nat.testBit x k then 1 else 0)).sum

def distance (x y : Nat) : Nat := popcount9 (Nat.xor x y)

def coefficient (d : Nat) : Int :=
  match d with
  | 0 => 128
  | 2 => -16
  | 4 => 8
  | 6 => -10
  | 8 => 35
  | _ => 0

def matrix (i j : Nat) : Int := coefficient (distance (point i) (point j))
def amplitude (i : Nat) : Int := 21 * chi i

def row (i : Nat) : Int :=
  ((List.range 8).map (fun j => matrix i j * amplitude j)).sum

theorem points_distinct : points.Nodup := by decide

theorem points_in_cube : forall i : Fin 8,
    point i.val < 512 := by decide

theorem points_even : forall i : Fin 8,
    popcount9 (point i.val) % 2 = 0 := by decide

theorem cubic_eigenvector : forall i : Fin 8,
    ((List.range 8).map (fun j => matrix i.val j * chi j)).sum =
      -15 * chi i.val := by decide

theorem explicit_matrix_solution : forall i : Fin 8,
    row i.val = 315 * (-chi i.val) := by decide

theorem rhs_is_ternary : forall i : Fin 8,
    And (-1 <= -chi i.val) (-chi i.val <= 1) := by decide

theorem amplitudes_exceed_count_bound : forall i : Fin 8,
    And ((amplitude i.val).natAbs = 21) (9 < (amplitude i.val).natAbs) := by decide

theorem solution_nonzero : amplitude 0 = 21 := by decide

#print axioms points_distinct
#print axioms points_in_cube
#print axioms points_even
#print axioms cubic_eigenvector
#print axioms explicit_matrix_solution
#print axioms rhs_is_ternary
#print axioms amplitudes_exceed_count_bound
#print axioms solution_nonzero

end EightCubeObstruction240
