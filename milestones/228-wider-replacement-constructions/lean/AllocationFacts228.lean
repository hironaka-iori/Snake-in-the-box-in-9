import Std

set_option Elab.async false
set_option maxRecDepth 4096

namespace AllocationFacts228

-- Literal extraction and face-capacity inputs are native, pinned separately.
-- This module checks only the resulting finite allocation arithmetic.
structure AllocationRow where
  context : Nat
  budget : Nat
  firstParity : Nat
  secondParity : Nat
  firstZeroAllowed : Bool
  secondZeroAllowed : Bool
  firstDesired : Nat
  secondDesired : Nat

def rows : List AllocationRow := [
  { context := 13, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 14, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 16, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 17, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 19, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 20, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 21, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 22, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 23, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 24, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 25, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 26, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 27, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 28, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 29, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 30, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 31, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 32, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 56, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 57, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 58, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 59, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 60, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 61, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 62, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 63, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 64, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 65, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 66, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 67, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 68, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 69, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 70, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 71, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 72, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 73, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 74, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 75, budget := 2, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 76, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 77, budget := 1, firstParity := 0, firstZeroAllowed := true, firstDesired := 0, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 88, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 89, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 90, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 91, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 92, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 93, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 94, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 95, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 96, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 97, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 98, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 99, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 100, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 101, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 102, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 103, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 104, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 105, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 106, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 107, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 108, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 109, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 110, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 111, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 112, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 113, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 114, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 115, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 116, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 117, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 118, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 119, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 120, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 121, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 132, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 133, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 134, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 135, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 136, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 137, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 138, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 139, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 140, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 141, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 142, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 143, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 144, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 145, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 146, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 147, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 148, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 149, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 150, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 151, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 152, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 153, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 154, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 155, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 156, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 157, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 158, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 159, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 160, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 161, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 162, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 163, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 164, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 176, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 177, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 178, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 179, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 180, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 181, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 182, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 183, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 184, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 185, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 186, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 187, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 188, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 189, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 190, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 191, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 192, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 193, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 194, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 195, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 196, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 197, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 198, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 199, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 200, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 201, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 202, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 203, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 204, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 205, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 206, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 207, budget := 3, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 0, secondZeroAllowed := false, secondDesired := 2 },
  { context := 208, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := true, secondDesired := 1 },
  { context := 220, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 221, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 222, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 223, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 224, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 225, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 226, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 227, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 228, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 229, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 230, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 231, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 232, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 },
  { context := 233, budget := 2, firstParity := 1, firstZeroAllowed := true, firstDesired := 1, secondParity := 1, secondZeroAllowed := false, secondDesired := 1 }
]

def checkRow (r : AllocationRow) : Bool :=
  (List.range (r.budget + 1)).all fun a =>
    (List.range (r.budget + 1)).all fun b =>
      decide ((a + b = r.budget ∧
        a % 2 = r.firstParity ∧ b % 2 = r.secondParity ∧
        (a = 0 → r.firstZeroAllowed = true) ∧
        (b = 0 → r.secondZeroAllowed = true)) →
        a = r.firstDesired ∧ b = r.secondDesired)

theorem row_count : rows.length = 154 := by decide

theorem all_allocations : rows.all checkRow = true := by decide

/-- Nonnegative crossing counts satisfying the pinned budget, parity and
zero-count permissions have the listed allocation. Actual-path parity and
face-capacity implications must be supplied separately. -/
theorem forced_allocation (r : AllocationRow) (hr : r ∈ rows)
    (a b : Nat) (hsum : a + b = r.budget)
    (hfirst : a % 2 = r.firstParity)
    (hsecond : b % 2 = r.secondParity)
    (hzeroFirst : a = 0 → r.firstZeroAllowed = true)
    (hzeroSecond : b = 0 → r.secondZeroAllowed = true) :
    a = r.firstDesired ∧ b = r.secondDesired := by
  have hrow := List.all_eq_true.mp all_allocations r hr
  change (List.range (r.budget + 1)).all (fun a =>
    (List.range (r.budget + 1)).all (fun b =>
      decide ((a + b = r.budget ∧
        a % 2 = r.firstParity ∧ b % 2 = r.secondParity ∧
        (a = 0 → r.firstZeroAllowed = true) ∧
        (b = 0 → r.secondZeroAllowed = true)) →
        a = r.firstDesired ∧ b = r.secondDesired))) = true at hrow
  have ha : a ∈ List.range (r.budget + 1) := List.mem_range.mpr (by omega)
  have hb : b ∈ List.range (r.budget + 1) := List.mem_range.mpr (by omega)
  have hpair := List.all_eq_true.mp (List.all_eq_true.mp hrow a ha) b hb
  have hforced :
      (a + b = r.budget ∧
        a % 2 = r.firstParity ∧ b % 2 = r.secondParity ∧
        (a = 0 → r.firstZeroAllowed = true) ∧
        (b = 0 → r.secondZeroAllowed = true)) →
        a = r.firstDesired ∧ b = r.secondDesired := by
    simpa only [decide_eq_true_eq] using hpair
  exact hforced ⟨hsum, hfirst, hsecond, hzeroFirst, hzeroSecond⟩

#print axioms row_count
#print axioms all_allocations
#print axioms forced_allocation

end AllocationFacts228
