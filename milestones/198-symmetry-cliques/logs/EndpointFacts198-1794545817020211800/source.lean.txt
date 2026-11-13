import EndpointVertex198_0
import EndpointVertex198_1
import EndpointVertex198_2
import EndpointVertex198_3
import EndpointVertex198_4
import EndpointVertex198_5
import EndpointVertex198_6
import EndpointVertex198_7
namespace EndpointData198

theorem involution (k : Fin 6) (v : Fin 128) :
 generator k (generator k v)=v := by
 refine cover (P:=fun v => generator k (generator k v)=v) ?_ v
 intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact EndpointVertex198_0.involution k i
 · exact EndpointVertex198_1.involution k i
 · exact EndpointVertex198_2.involution k i
 · exact EndpointVertex198_3.involution k i
 · exact EndpointVertex198_4.involution k i
 · exact EndpointVertex198_5.involution k i
 · exact EndpointVertex198_6.involution k i
 · exact EndpointVertex198_7.involution k i

theorem normalized (v : Fin 128) :
 (evaluate (word v) v).val=10 ∨ (evaluate (word v) v).val=2 ∨ (evaluate (word v) v).val=0 := by
 refine cover (P:=fun v => (evaluate (word v) v).val=10 ∨ (evaluate (word v) v).val=2 ∨ (evaluate (word v) v).val=0) ?_ v
 intro b i
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 ∨ b=4 ∨ b=5 ∨ b=6 ∨ b=7 := by omega
 rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact EndpointVertex198_0.normalized i
 · exact EndpointVertex198_1.normalized i
 · exact EndpointVertex198_2.normalized i
 · exact EndpointVertex198_3.normalized i
 · exact EndpointVertex198_4.normalized i
 · exact EndpointVertex198_5.normalized i
 · exact EndpointVertex198_6.normalized i
 · exact EndpointVertex198_7.normalized i

#print axioms involution
#print axioms normalized
end EndpointData198
