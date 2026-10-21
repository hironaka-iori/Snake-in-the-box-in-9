import ParallelShareApplicability.ParallelShare00.Check75Part0
import ParallelShareApplicability.ParallelShare00.Check75Part1
import ParallelShareApplicability.ParallelShare00.Check75Part2
import ParallelShareApplicability.ParallelShare00.Check75Part3
import ParallelShareApplicability.ParallelShare00.Check75Part4
import ParallelShareApplicability.ParallelShare00.Check75Part5
import ParallelShareApplicability.ParallelShare00.Check75Part6
import ParallelShareApplicability.ParallelShare00.Check75Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts75Refined : List (List Tag × List (List Nat)) := [((tags75.drop 0).take 16, (raw75.drop 0).take 16), ((tags75.drop 16).take 16, (raw75.drop 16).take 16), ((tags75.drop 32).take 16, (raw75.drop 32).take 16), ((tags75.drop 48).take 16, (raw75.drop 48).take 16), ((tags75.drop 64).take 16, (raw75.drop 64).take 16), ((tags75.drop 80).take 16, (raw75.drop 80).take 16), ((tags75.drop 96).take 16, (raw75.drop 96).take 16), ((tags75.drop 112).take 16, (raw75.drop 112).take 16)]

theorem check75 : checkRaw oldMeaning ctrs window terms meaning 20 tags75 raw75 = true := by
  have ht : parts75Refined.flatMap Prod.fst = tags75 := by rfl
  have hr : parts75Refined.flatMap Prod.snd = raw75 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts75Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check75Part0
  · exact check75Part1
  · exact check75Part2
  · exact check75Part3
  · exact check75Part4
  · exact check75Part5
  · exact check75Part6
  · exact check75Part7
end Snake9.LocalWindow.ParallelShare00Applicability
