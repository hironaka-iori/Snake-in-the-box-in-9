import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_sort6 : pw epVerts6 = true := by decide +kernel
#print axioms ep_sort6
theorem ep_cross6 : epVerts6.all (fun x => (epVerts7 ++ epVerts8 ++ epVerts9 ++ epVerts10 ++ epVerts11 ++ epVerts12 ++ epVerts13 ++ epVerts14 ++ epVerts15 ++ epVerts16 ++ epVerts17).all (fun y => decide (x < y))) = true := by decide +kernel
#print axioms ep_cross6
end Snake9.LocalWindow.ShareWindow185
