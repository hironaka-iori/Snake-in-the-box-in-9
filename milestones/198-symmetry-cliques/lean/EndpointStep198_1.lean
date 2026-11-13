import EndpointChunk198_1_0
import EndpointChunk198_1_1
import EndpointChunk198_1_2
import EndpointChunk198_1_3
import EndpointChunk198_1_4
import EndpointChunk198_1_5
import EndpointChunk198_1_6
import EndpointChunk198_1_7
namespace EndpointStep198_1
open EndpointData198

theorem step (v : Fin 128) (d : Fin 8) :
 generator ⟨1,by decide⟩ (neighbour v d) = neighbour (generator ⟨1,by decide⟩ v) (direction ⟨1,by decide⟩ d) := by
 refine cover (P:=fun v => generator ⟨1,by decide⟩ (neighbour v d) = neighbour (generator ⟨1,by decide⟩ v) (direction ⟨1,by decide⟩ d)) ?_ v
 intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact EndpointChunk198_1_0.step i d
 · exact EndpointChunk198_1_1.step i d
 · exact EndpointChunk198_1_2.step i d
 · exact EndpointChunk198_1_3.step i d
 · exact EndpointChunk198_1_4.step i d
 · exact EndpointChunk198_1_5.step i d
 · exact EndpointChunk198_1_6.step i d
 · exact EndpointChunk198_1_7.step i d

#print axioms step
end EndpointStep198_1
