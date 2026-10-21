import ParallelShareApplicability.ParallelShare00.Check58Part0
import ParallelShareApplicability.ParallelShare00.Check58Part1
import ParallelShareApplicability.ParallelShare00.Check58Part2
import ParallelShareApplicability.ParallelShare00.Check58Part3
import ParallelShareApplicability.ParallelShare00.Check58Part4
import ParallelShareApplicability.ParallelShare00.Check58Part5
import ParallelShareApplicability.ParallelShare00.Check58Part6
import ParallelShareApplicability.ParallelShare00.Check58Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts58Refined : List (List Tag × List (List Nat)) := [((tags58.drop 0).take 16, (raw58.drop 0).take 16), ((tags58.drop 16).take 16, (raw58.drop 16).take 16), ((tags58.drop 32).take 16, (raw58.drop 32).take 16), ((tags58.drop 48).take 16, (raw58.drop 48).take 16), ((tags58.drop 64).take 16, (raw58.drop 64).take 16), ((tags58.drop 80).take 16, (raw58.drop 80).take 16), ((tags58.drop 96).take 16, (raw58.drop 96).take 16), ((tags58.drop 112).take 16, (raw58.drop 112).take 16)]

theorem check58 : checkRaw oldMeaning ctrs window terms meaning 20 tags58 raw58 = true := by
  have ht : parts58Refined.flatMap Prod.fst = tags58 := by rfl
  have hr : parts58Refined.flatMap Prod.snd = raw58 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts58Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check58Part0
  · exact check58Part1
  · exact check58Part2
  · exact check58Part3
  · exact check58Part4
  · exact check58Part5
  · exact check58Part6
  · exact check58Part7
end Snake9.LocalWindow.ParallelShare00Applicability
