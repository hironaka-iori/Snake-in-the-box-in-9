import EndpointChunk198_4_0
import EndpointChunk198_4_1
import EndpointChunk198_4_2
import EndpointChunk198_4_3
import EndpointChunk198_4_4
import EndpointChunk198_4_5
import EndpointChunk198_4_6
import EndpointChunk198_4_7
namespace EndpointStep198_4
open EndpointData198

theorem step (v : Fin 128) (d : Fin 8) :
 generator ⟨4,by decide⟩ (neighbour v d) = neighbour (generator ⟨4,by decide⟩ v) (direction ⟨4,by decide⟩ d) := by
 refine cover (P:=fun v => generator ⟨4,by decide⟩ (neighbour v d) = neighbour (generator ⟨4,by decide⟩ v) (direction ⟨4,by decide⟩ d)) ?_ v
 intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact EndpointChunk198_4_0.step i d
 · exact EndpointChunk198_4_1.step i d
 · exact EndpointChunk198_4_2.step i d
 · exact EndpointChunk198_4_3.step i d
 · exact EndpointChunk198_4_4.step i d
 · exact EndpointChunk198_4_5.step i d
 · exact EndpointChunk198_4_6.step i d
 · exact EndpointChunk198_4_7.step i d

#print axioms step
end EndpointStep198_4
