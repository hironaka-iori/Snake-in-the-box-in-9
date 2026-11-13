import EndpointData198
namespace EndpointChunk198_5_2
open EndpointData198
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem step : ∀ i : Fin 16, ∀ d : Fin 8,
 let v : Fin 128 := ⟨32+i.val,by omega⟩
 generator ⟨5,by decide⟩ (neighbour v d) = neighbour (generator ⟨5,by decide⟩ v) (direction ⟨5,by decide⟩ d) := by decide +kernel

#print axioms step
end EndpointChunk198_5_2
