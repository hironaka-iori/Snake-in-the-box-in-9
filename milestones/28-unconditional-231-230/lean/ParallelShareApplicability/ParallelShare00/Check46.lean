import ParallelShareApplicability.ParallelShare00.Check46Part0
import ParallelShareApplicability.ParallelShare00.Check46Part1
import ParallelShareApplicability.ParallelShare00.Check46Part2
import ParallelShareApplicability.ParallelShare00.Check46Part3
import ParallelShareApplicability.ParallelShare00.Check46Part4
import ParallelShareApplicability.ParallelShare00.Check46Part5
import ParallelShareApplicability.ParallelShare00.Check46Part6
import ParallelShareApplicability.ParallelShare00.Check46Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts46Refined : List (List Tag × List (List Nat)) := [((tags46.drop 0).take 16, (raw46.drop 0).take 16), ((tags46.drop 16).take 16, (raw46.drop 16).take 16), ((tags46.drop 32).take 16, (raw46.drop 32).take 16), ((tags46.drop 48).take 16, (raw46.drop 48).take 16), ((tags46.drop 64).take 16, (raw46.drop 64).take 16), ((tags46.drop 80).take 16, (raw46.drop 80).take 16), ((tags46.drop 96).take 16, (raw46.drop 96).take 16), ((tags46.drop 112).take 16, (raw46.drop 112).take 16)]

theorem check46 : checkRaw oldMeaning ctrs window terms meaning 20 tags46 raw46 = true := by
  have ht : parts46Refined.flatMap Prod.fst = tags46 := by rfl
  have hr : parts46Refined.flatMap Prod.snd = raw46 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts46Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check46Part0
  · exact check46Part1
  · exact check46Part2
  · exact check46Part3
  · exact check46Part4
  · exact check46Part5
  · exact check46Part6
  · exact check46Part7
end Snake9.LocalWindow.ParallelShare00Applicability
