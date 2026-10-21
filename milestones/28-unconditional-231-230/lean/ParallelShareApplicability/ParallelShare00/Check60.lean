import ParallelShareApplicability.ParallelShare00.Check60Part0
import ParallelShareApplicability.ParallelShare00.Check60Part1
import ParallelShareApplicability.ParallelShare00.Check60Part2
import ParallelShareApplicability.ParallelShare00.Check60Part3
import ParallelShareApplicability.ParallelShare00.Check60Part4
import ParallelShareApplicability.ParallelShare00.Check60Part5
import ParallelShareApplicability.ParallelShare00.Check60Part6
import ParallelShareApplicability.ParallelShare00.Check60Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts60Refined : List (List Tag × List (List Nat)) := [((tags60.drop 0).take 16, (raw60.drop 0).take 16), ((tags60.drop 16).take 16, (raw60.drop 16).take 16), ((tags60.drop 32).take 16, (raw60.drop 32).take 16), ((tags60.drop 48).take 16, (raw60.drop 48).take 16), ((tags60.drop 64).take 16, (raw60.drop 64).take 16), ((tags60.drop 80).take 16, (raw60.drop 80).take 16), ((tags60.drop 96).take 16, (raw60.drop 96).take 16), ((tags60.drop 112).take 16, (raw60.drop 112).take 16)]

theorem check60 : checkRaw oldMeaning ctrs window terms meaning 20 tags60 raw60 = true := by
  have ht : parts60Refined.flatMap Prod.fst = tags60 := by rfl
  have hr : parts60Refined.flatMap Prod.snd = raw60 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts60Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check60Part0
  · exact check60Part1
  · exact check60Part2
  · exact check60Part3
  · exact check60Part4
  · exact check60Part5
  · exact check60Part6
  · exact check60Part7
end Snake9.LocalWindow.ParallelShare00Applicability
