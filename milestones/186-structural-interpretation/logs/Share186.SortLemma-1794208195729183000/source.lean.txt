import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem pw_append (a b : List Nat) :
 pw (a ++ b) = (a.all (fun x => b.all (fun y => decide (x < y))) && pw a && pw b) := by
 induction a with
 | nil => simp [pw]
 | cons x xs ih =>
   simp only [List.cons_append,pw,List.all_append,ih,List.all_cons,
     Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
#print axioms pw_append
end Snake9.LocalWindow.ShareWindow185
