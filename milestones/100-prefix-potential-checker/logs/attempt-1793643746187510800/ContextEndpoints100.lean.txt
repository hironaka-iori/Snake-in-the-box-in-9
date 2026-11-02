import StateWalk

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.ContextEndpoints100
open Snake9.GraphWalk78

theorem source35 (code : Nat) :
    edgeSource 0 35 code = 77760 + code/6 := by rfl

theorem target35 (code : Nat) :
    edgeTarget 0 35 code = 1049760 + code%7776 := by rfl

theorem source177 (code : Nat) :
    edgeSource 43 177 code = 1353024 + code/6 := by rfl

theorem target177 (code : Nat) :
    edgeTarget 43 177 code = 1500768 + code%7776 := by rfl

#print axioms source35
#print axioms target35
#print axioms source177
#print axioms target177
end Snake9.ContextEndpoints100
