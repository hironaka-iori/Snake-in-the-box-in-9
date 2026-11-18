import CubeInverseKernel237_00
import CubeInverseKernel237_01
import CubeInverseKernel237_02
import CubeInverseKernel237_03
import CubeInverseKernel237_04
import CubeInverseKernel237_05
import CubeInverseKernel237_06
import CubeInverseKernel237_07
import CubeInverseKernel237_08
import CubeInverseKernel237_09
import CubeInverseKernel237_10
import CubeInverseKernel237_11
import CubeInverseKernel237_12
import CubeInverseKernel237_13
import CubeInverseKernel237_14
import CubeInverseKernel237_15

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

namespace CubeInverse

private theorem kernel_origin (x : Vertex 9) :
    flipSum 9 (fun y => coefficient (weight 9 y)) x = spike 9 x := by
  rcases x with ⟨b0, b1, b2, b3, tail⟩
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3
  · exact kernel_case_00 tail
  · exact kernel_case_01 tail
  · exact kernel_case_02 tail
  · exact kernel_case_03 tail
  · exact kernel_case_04 tail
  · exact kernel_case_05 tail
  · exact kernel_case_06 tail
  · exact kernel_case_07 tail
  · exact kernel_case_08 tail
  · exact kernel_case_09 tail
  · exact kernel_case_10 tail
  · exact kernel_case_11 tail
  · exact kernel_case_12 tail
  · exact kernel_case_13 tail
  · exact kernel_case_14 tail
  · exact kernel_case_15 tail

/-- Exact inverse for the ordinary one-coordinate-flip neighbour sum on Q9.
The sum in the left hand side is over all 512 bit vectors. -/
theorem reconstruct (z : Vertex 9 → Int) (a : Vertex 9) :
    inner 9 (fun x => coefficient (weight 9 (translate 9 a x))) (flipSum 9 z)
      = 315 * z a := by
  rw [self_adjoint]
  have h : flipSum 9 (fun x => coefficient (weight 9 (translate 9 a x))) =
      fun x => spike 9 (translate 9 a x) := by
    funext x
    exact (flip_translate 9 (fun y => coefficient (weight 9 y)) a x).trans
      (kernel_origin _)
  rw [h, inner_spike]

theorem neighbour_sum_injective (f g : Vertex 9 → Int)
    (h : flipSum 9 f = flipSum 9 g) : f = g := by
  funext a
  have hf := reconstruct f a
  have hg := reconstruct g a
  rw [h] at hf
  omega

#print axioms reconstruct
#print axioms neighbour_sum_injective


end CubeInverse
