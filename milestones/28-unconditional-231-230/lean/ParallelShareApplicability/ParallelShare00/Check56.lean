import ParallelShareApplicability.ParallelShare00.Check56Part0
import ParallelShareApplicability.ParallelShare00.Check56Part1
import ParallelShareApplicability.ParallelShare00.Check56Part2
import ParallelShareApplicability.ParallelShare00.Check56Part3
import ParallelShareApplicability.ParallelShare00.Check56Part4
import ParallelShareApplicability.ParallelShare00.Check56Part5
import ParallelShareApplicability.ParallelShare00.Check56Part6
import ParallelShareApplicability.ParallelShare00.Check56Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts56Refined : List (List Tag × List (List Nat)) := [((tags56.drop 0).take 16, (raw56.drop 0).take 16), ((tags56.drop 16).take 16, (raw56.drop 16).take 16), ((tags56.drop 32).take 16, (raw56.drop 32).take 16), ((tags56.drop 48).take 16, (raw56.drop 48).take 16), ((tags56.drop 64).take 16, (raw56.drop 64).take 16), ((tags56.drop 80).take 16, (raw56.drop 80).take 16), ((tags56.drop 96).take 16, (raw56.drop 96).take 16), ((tags56.drop 112).take 16, (raw56.drop 112).take 16)]

theorem check56 : checkRaw oldMeaning ctrs window terms meaning 20 tags56 raw56 = true := by
  have ht : parts56Refined.flatMap Prod.fst = tags56 := by rfl
  have hr : parts56Refined.flatMap Prod.snd = raw56 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts56Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check56Part0
  · exact check56Part1
  · exact check56Part2
  · exact check56Part3
  · exact check56Part4
  · exact check56Part5
  · exact check56Part6
  · exact check56Part7
end Snake9.LocalWindow.ParallelShare00Applicability
