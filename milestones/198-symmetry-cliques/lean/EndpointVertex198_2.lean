import EndpointData198
namespace EndpointVertex198_2
open EndpointData198
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem involution : ∀ k : Fin 6, ∀ i : Fin 16,
 let v : Fin 128 := ⟨32+i.val,by omega⟩
 generator k (generator k v)=v := by decide +kernel

theorem normalized : ∀ i : Fin 16,
 let v : Fin 128 := ⟨32+i.val,by omega⟩
 (evaluate (word v) v).val=10 ∨ (evaluate (word v) v).val=2 ∨ (evaluate (word v) v).val=0 := by decide +kernel

#print axioms involution
#print axioms normalized
end EndpointVertex198_2
