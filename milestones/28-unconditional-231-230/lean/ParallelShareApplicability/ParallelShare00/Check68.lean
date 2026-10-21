import ParallelShareApplicability.ParallelShare00.Check68Part0
import ParallelShareApplicability.ParallelShare00.Check68Part1
import ParallelShareApplicability.ParallelShare00.Check68Part2
import ParallelShareApplicability.ParallelShare00.Check68Part3
import ParallelShareApplicability.ParallelShare00.Check68Part4
import ParallelShareApplicability.ParallelShare00.Check68Part5
import ParallelShareApplicability.ParallelShare00.Check68Part6
import ParallelShareApplicability.ParallelShare00.Check68Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts68Refined : List (List Tag × List (List Nat)) := [((tags68.drop 0).take 16, (raw68.drop 0).take 16), ((tags68.drop 16).take 16, (raw68.drop 16).take 16), ((tags68.drop 32).take 16, (raw68.drop 32).take 16), ((tags68.drop 48).take 16, (raw68.drop 48).take 16), ((tags68.drop 64).take 16, (raw68.drop 64).take 16), ((tags68.drop 80).take 16, (raw68.drop 80).take 16), ((tags68.drop 96).take 16, (raw68.drop 96).take 16), ((tags68.drop 112).take 16, (raw68.drop 112).take 16)]

theorem check68 : checkRaw oldMeaning ctrs window terms meaning 20 tags68 raw68 = true := by
  have ht : parts68Refined.flatMap Prod.fst = tags68 := by rfl
  have hr : parts68Refined.flatMap Prod.snd = raw68 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts68Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check68Part0
  · exact check68Part1
  · exact check68Part2
  · exact check68Part3
  · exact check68Part4
  · exact check68Part5
  · exact check68Part6
  · exact check68Part7
end Snake9.LocalWindow.ParallelShare00Applicability
