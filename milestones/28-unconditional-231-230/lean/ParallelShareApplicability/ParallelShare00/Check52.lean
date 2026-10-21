import ParallelShareApplicability.ParallelShare00.Check52Part0
import ParallelShareApplicability.ParallelShare00.Check52Part1
import ParallelShareApplicability.ParallelShare00.Check52Part2
import ParallelShareApplicability.ParallelShare00.Check52Part3
import ParallelShareApplicability.ParallelShare00.Check52Part4
import ParallelShareApplicability.ParallelShare00.Check52Part5
import ParallelShareApplicability.ParallelShare00.Check52Part6
import ParallelShareApplicability.ParallelShare00.Check52Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts52Refined : List (List Tag × List (List Nat)) := [((tags52.drop 0).take 16, (raw52.drop 0).take 16), ((tags52.drop 16).take 16, (raw52.drop 16).take 16), ((tags52.drop 32).take 16, (raw52.drop 32).take 16), ((tags52.drop 48).take 16, (raw52.drop 48).take 16), ((tags52.drop 64).take 16, (raw52.drop 64).take 16), ((tags52.drop 80).take 16, (raw52.drop 80).take 16), ((tags52.drop 96).take 16, (raw52.drop 96).take 16), ((tags52.drop 112).take 16, (raw52.drop 112).take 16)]

theorem check52 : checkRaw oldMeaning ctrs window terms meaning 20 tags52 raw52 = true := by
  have ht : parts52Refined.flatMap Prod.fst = tags52 := by rfl
  have hr : parts52Refined.flatMap Prod.snd = raw52 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts52Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check52Part0
  · exact check52Part1
  · exact check52Part2
  · exact check52Part3
  · exact check52Part4
  · exact check52Part5
  · exact check52Part6
  · exact check52Part7
end Snake9.LocalWindow.ParallelShare00Applicability
