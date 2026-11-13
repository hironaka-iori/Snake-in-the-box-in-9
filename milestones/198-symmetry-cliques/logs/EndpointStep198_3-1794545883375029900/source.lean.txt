import EndpointChunk198_3_0
import EndpointChunk198_3_1
import EndpointChunk198_3_2
import EndpointChunk198_3_3
import EndpointChunk198_3_4
import EndpointChunk198_3_5
import EndpointChunk198_3_6
import EndpointChunk198_3_7
namespace EndpointStep198_3
open EndpointData198

theorem step (v : Fin 128) (d : Fin 8) :
 generator ⟨3,by decide⟩ (neighbour v d) = neighbour (generator ⟨3,by decide⟩ v) (direction ⟨3,by decide⟩ d) := by
 refine cover (P:=fun v => generator ⟨3,by decide⟩ (neighbour v d) = neighbour (generator ⟨3,by decide⟩ v) (direction ⟨3,by decide⟩ d)) ?_ v
 intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact EndpointChunk198_3_0.step i d
 · exact EndpointChunk198_3_1.step i d
 · exact EndpointChunk198_3_2.step i d
 · exact EndpointChunk198_3_3.step i d
 · exact EndpointChunk198_3_4.step i d
 · exact EndpointChunk198_3_5.step i d
 · exact EndpointChunk198_3_6.step i d
 · exact EndpointChunk198_3_7.step i d

#print axioms step
end EndpointStep198_3
