import ParallelShareApplicability.ParallelShare00.Check65Part0
import ParallelShareApplicability.ParallelShare00.Check65Part1
import ParallelShareApplicability.ParallelShare00.Check65Part2
import ParallelShareApplicability.ParallelShare00.Check65Part3
import ParallelShareApplicability.ParallelShare00.Check65Part4
import ParallelShareApplicability.ParallelShare00.Check65Part5
import ParallelShareApplicability.ParallelShare00.Check65Part6
import ParallelShareApplicability.ParallelShare00.Check65Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts65Refined : List (List Tag × List (List Nat)) := [((tags65.drop 0).take 16, (raw65.drop 0).take 16), ((tags65.drop 16).take 16, (raw65.drop 16).take 16), ((tags65.drop 32).take 16, (raw65.drop 32).take 16), ((tags65.drop 48).take 16, (raw65.drop 48).take 16), ((tags65.drop 64).take 16, (raw65.drop 64).take 16), ((tags65.drop 80).take 16, (raw65.drop 80).take 16), ((tags65.drop 96).take 16, (raw65.drop 96).take 16), ((tags65.drop 112).take 16, (raw65.drop 112).take 16)]

theorem check65 : checkRaw oldMeaning ctrs window terms meaning 20 tags65 raw65 = true := by
  have ht : parts65Refined.flatMap Prod.fst = tags65 := by rfl
  have hr : parts65Refined.flatMap Prod.snd = raw65 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts65Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check65Part0
  · exact check65Part1
  · exact check65Part2
  · exact check65Part3
  · exact check65Part4
  · exact check65Part5
  · exact check65Part6
  · exact check65Part7
end Snake9.LocalWindow.ParallelShare00Applicability
