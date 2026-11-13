import EndpointChunk198_5_0
import EndpointChunk198_5_1
import EndpointChunk198_5_2
import EndpointChunk198_5_3
import EndpointChunk198_5_4
import EndpointChunk198_5_5
import EndpointChunk198_5_6
import EndpointChunk198_5_7
namespace EndpointStep198_5
open EndpointData198

theorem step (v : Fin 128) (d : Fin 8) :
 generator ⟨5,by decide⟩ (neighbour v d) = neighbour (generator ⟨5,by decide⟩ v) (direction ⟨5,by decide⟩ d) := by
 refine cover (P:=fun v => generator ⟨5,by decide⟩ (neighbour v d) = neighbour (generator ⟨5,by decide⟩ v) (direction ⟨5,by decide⟩ d)) ?_ v
 intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact EndpointChunk198_5_0.step i d
 · exact EndpointChunk198_5_1.step i d
 · exact EndpointChunk198_5_2.step i d
 · exact EndpointChunk198_5_3.step i d
 · exact EndpointChunk198_5_4.step i d
 · exact EndpointChunk198_5_5.step i d
 · exact EndpointChunk198_5_6.step i d
 · exact EndpointChunk198_5_7.step i d

#print axioms step
end EndpointStep198_5
