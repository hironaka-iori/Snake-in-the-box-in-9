import ParallelShareApplicability.ParallelShare00.Check66Part0
import ParallelShareApplicability.ParallelShare00.Check66Part1
import ParallelShareApplicability.ParallelShare00.Check66Part2
import ParallelShareApplicability.ParallelShare00.Check66Part3
import ParallelShareApplicability.ParallelShare00.Check66Part4
import ParallelShareApplicability.ParallelShare00.Check66Part5
import ParallelShareApplicability.ParallelShare00.Check66Part6
import ParallelShareApplicability.ParallelShare00.Check66Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts66Refined : List (List Tag × List (List Nat)) := [((tags66.drop 0).take 16, (raw66.drop 0).take 16), ((tags66.drop 16).take 16, (raw66.drop 16).take 16), ((tags66.drop 32).take 16, (raw66.drop 32).take 16), ((tags66.drop 48).take 16, (raw66.drop 48).take 16), ((tags66.drop 64).take 16, (raw66.drop 64).take 16), ((tags66.drop 80).take 16, (raw66.drop 80).take 16), ((tags66.drop 96).take 16, (raw66.drop 96).take 16), ((tags66.drop 112).take 16, (raw66.drop 112).take 16)]

theorem check66 : checkRaw oldMeaning ctrs window terms meaning 20 tags66 raw66 = true := by
  have ht : parts66Refined.flatMap Prod.fst = tags66 := by rfl
  have hr : parts66Refined.flatMap Prod.snd = raw66 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts66Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check66Part0
  · exact check66Part1
  · exact check66Part2
  · exact check66Part3
  · exact check66Part4
  · exact check66Part5
  · exact check66Part6
  · exact check66Part7
end Snake9.LocalWindow.ParallelShare00Applicability
