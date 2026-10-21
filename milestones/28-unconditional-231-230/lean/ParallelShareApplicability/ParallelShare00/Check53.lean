import ParallelShareApplicability.ParallelShare00.Check53Part0
import ParallelShareApplicability.ParallelShare00.Check53Part1
import ParallelShareApplicability.ParallelShare00.Check53Part2
import ParallelShareApplicability.ParallelShare00.Check53Part3
import ParallelShareApplicability.ParallelShare00.Check53Part4
import ParallelShareApplicability.ParallelShare00.Check53Part5
import ParallelShareApplicability.ParallelShare00.Check53Part6
import ParallelShareApplicability.ParallelShare00.Check53Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts53Refined : List (List Tag × List (List Nat)) := [((tags53.drop 0).take 16, (raw53.drop 0).take 16), ((tags53.drop 16).take 16, (raw53.drop 16).take 16), ((tags53.drop 32).take 16, (raw53.drop 32).take 16), ((tags53.drop 48).take 16, (raw53.drop 48).take 16), ((tags53.drop 64).take 16, (raw53.drop 64).take 16), ((tags53.drop 80).take 16, (raw53.drop 80).take 16), ((tags53.drop 96).take 16, (raw53.drop 96).take 16), ((tags53.drop 112).take 16, (raw53.drop 112).take 16)]

theorem check53 : checkRaw oldMeaning ctrs window terms meaning 20 tags53 raw53 = true := by
  have ht : parts53Refined.flatMap Prod.fst = tags53 := by rfl
  have hr : parts53Refined.flatMap Prod.snd = raw53 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts53Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check53Part0
  · exact check53Part1
  · exact check53Part2
  · exact check53Part3
  · exact check53Part4
  · exact check53Part5
  · exact check53Part6
  · exact check53Part7
end Snake9.LocalWindow.ParallelShare00Applicability
