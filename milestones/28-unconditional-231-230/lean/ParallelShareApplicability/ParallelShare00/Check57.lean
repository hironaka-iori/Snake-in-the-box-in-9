import ParallelShareApplicability.ParallelShare00.Check57Part0
import ParallelShareApplicability.ParallelShare00.Check57Part1
import ParallelShareApplicability.ParallelShare00.Check57Part2
import ParallelShareApplicability.ParallelShare00.Check57Part3
import ParallelShareApplicability.ParallelShare00.Check57Part4
import ParallelShareApplicability.ParallelShare00.Check57Part5
import ParallelShareApplicability.ParallelShare00.Check57Part6
import ParallelShareApplicability.ParallelShare00.Check57Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts57Refined : List (List Tag × List (List Nat)) := [((tags57.drop 0).take 16, (raw57.drop 0).take 16), ((tags57.drop 16).take 16, (raw57.drop 16).take 16), ((tags57.drop 32).take 16, (raw57.drop 32).take 16), ((tags57.drop 48).take 16, (raw57.drop 48).take 16), ((tags57.drop 64).take 16, (raw57.drop 64).take 16), ((tags57.drop 80).take 16, (raw57.drop 80).take 16), ((tags57.drop 96).take 16, (raw57.drop 96).take 16), ((tags57.drop 112).take 16, (raw57.drop 112).take 16)]

theorem check57 : checkRaw oldMeaning ctrs window terms meaning 20 tags57 raw57 = true := by
  have ht : parts57Refined.flatMap Prod.fst = tags57 := by rfl
  have hr : parts57Refined.flatMap Prod.snd = raw57 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts57Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check57Part0
  · exact check57Part1
  · exact check57Part2
  · exact check57Part3
  · exact check57Part4
  · exact check57Part5
  · exact check57Part6
  · exact check57Part7
end Snake9.LocalWindow.ParallelShare00Applicability
