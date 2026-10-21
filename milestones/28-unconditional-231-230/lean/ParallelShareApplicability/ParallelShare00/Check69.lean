import ParallelShareApplicability.ParallelShare00.Check69Part0
import ParallelShareApplicability.ParallelShare00.Check69Part1
import ParallelShareApplicability.ParallelShare00.Check69Part2
import ParallelShareApplicability.ParallelShare00.Check69Part3
import ParallelShareApplicability.ParallelShare00.Check69Part4
import ParallelShareApplicability.ParallelShare00.Check69Part5
import ParallelShareApplicability.ParallelShare00.Check69Part6
import ParallelShareApplicability.ParallelShare00.Check69Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts69Refined : List (List Tag × List (List Nat)) := [((tags69.drop 0).take 16, (raw69.drop 0).take 16), ((tags69.drop 16).take 16, (raw69.drop 16).take 16), ((tags69.drop 32).take 16, (raw69.drop 32).take 16), ((tags69.drop 48).take 16, (raw69.drop 48).take 16), ((tags69.drop 64).take 16, (raw69.drop 64).take 16), ((tags69.drop 80).take 16, (raw69.drop 80).take 16), ((tags69.drop 96).take 16, (raw69.drop 96).take 16), ((tags69.drop 112).take 16, (raw69.drop 112).take 16)]

theorem check69 : checkRaw oldMeaning ctrs window terms meaning 20 tags69 raw69 = true := by
  have ht : parts69Refined.flatMap Prod.fst = tags69 := by rfl
  have hr : parts69Refined.flatMap Prod.snd = raw69 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts69Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check69Part0
  · exact check69Part1
  · exact check69Part2
  · exact check69Part3
  · exact check69Part4
  · exact check69Part5
  · exact check69Part6
  · exact check69Part7
end Snake9.LocalWindow.ParallelShare00Applicability
