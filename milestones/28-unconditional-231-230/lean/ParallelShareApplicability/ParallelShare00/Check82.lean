import ParallelShareApplicability.ParallelShare00.Check82Part0
import ParallelShareApplicability.ParallelShare00.Check82Part1
import ParallelShareApplicability.ParallelShare00.Check82Part2
import ParallelShareApplicability.ParallelShare00.Check82Part3
import ParallelShareApplicability.ParallelShare00.Check82Part4
import ParallelShareApplicability.ParallelShare00.Check82Part5
import ParallelShareApplicability.ParallelShare00.Check82Part6
import ParallelShareApplicability.ParallelShare00.Check82Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts82Refined : List (List Tag × List (List Nat)) := [((tags82.drop 0).take 16, (raw82.drop 0).take 16), ((tags82.drop 16).take 16, (raw82.drop 16).take 16), ((tags82.drop 32).take 16, (raw82.drop 32).take 16), ((tags82.drop 48).take 16, (raw82.drop 48).take 16), ((tags82.drop 64).take 16, (raw82.drop 64).take 16), ((tags82.drop 80).take 16, (raw82.drop 80).take 16), ((tags82.drop 96).take 16, (raw82.drop 96).take 16), ((tags82.drop 112).take 16, (raw82.drop 112).take 16)]

theorem check82 : checkRaw oldMeaning ctrs window terms meaning 20 tags82 raw82 = true := by
  have ht : parts82Refined.flatMap Prod.fst = tags82 := by rfl
  have hr : parts82Refined.flatMap Prod.snd = raw82 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts82Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check82Part0
  · exact check82Part1
  · exact check82Part2
  · exact check82Part3
  · exact check82Part4
  · exact check82Part5
  · exact check82Part6
  · exact check82Part7
end Snake9.LocalWindow.ParallelShare00Applicability
