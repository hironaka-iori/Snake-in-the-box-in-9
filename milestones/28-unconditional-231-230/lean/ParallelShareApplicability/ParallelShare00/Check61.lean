import ParallelShareApplicability.ParallelShare00.Check61Part0
import ParallelShareApplicability.ParallelShare00.Check61Part1
import ParallelShareApplicability.ParallelShare00.Check61Part2
import ParallelShareApplicability.ParallelShare00.Check61Part3
import ParallelShareApplicability.ParallelShare00.Check61Part4
import ParallelShareApplicability.ParallelShare00.Check61Part5
import ParallelShareApplicability.ParallelShare00.Check61Part6
import ParallelShareApplicability.ParallelShare00.Check61Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts61Refined : List (List Tag × List (List Nat)) := [((tags61.drop 0).take 16, (raw61.drop 0).take 16), ((tags61.drop 16).take 16, (raw61.drop 16).take 16), ((tags61.drop 32).take 16, (raw61.drop 32).take 16), ((tags61.drop 48).take 16, (raw61.drop 48).take 16), ((tags61.drop 64).take 16, (raw61.drop 64).take 16), ((tags61.drop 80).take 16, (raw61.drop 80).take 16), ((tags61.drop 96).take 16, (raw61.drop 96).take 16), ((tags61.drop 112).take 16, (raw61.drop 112).take 16)]

theorem check61 : checkRaw oldMeaning ctrs window terms meaning 20 tags61 raw61 = true := by
  have ht : parts61Refined.flatMap Prod.fst = tags61 := by rfl
  have hr : parts61Refined.flatMap Prod.snd = raw61 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts61Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check61Part0
  · exact check61Part1
  · exact check61Part2
  · exact check61Part3
  · exact check61Part4
  · exact check61Part5
  · exact check61Part6
  · exact check61Part7
end Snake9.LocalWindow.ParallelShare00Applicability
