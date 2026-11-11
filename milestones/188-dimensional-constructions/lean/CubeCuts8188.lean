import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem displayed_cut_indices : (List.range 98).filter (fun i => transitions[i]! == 5) = [8, 34, 45, 71] := by decide +kernel
#print axioms displayed_cut_indices
end Dimensional188.Witness8
