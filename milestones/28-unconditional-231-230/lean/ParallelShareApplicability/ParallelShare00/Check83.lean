import ParallelShareApplicability.ParallelShare00.Check83Part0
import ParallelShareApplicability.ParallelShare00.Check83Part1
import ParallelShareApplicability.ParallelShare00.Check83Part2
import ParallelShareApplicability.ParallelShare00.Check83Part3
import ParallelShareApplicability.ParallelShare00.Check83Part4
import ParallelShareApplicability.ParallelShare00.Check83Part5
import ParallelShareApplicability.ParallelShare00.Check83Part6
import ParallelShareApplicability.ParallelShare00.Check83Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts83Refined : List (List Tag × List (List Nat)) := [((tags83.drop 0).take 16, (raw83.drop 0).take 16), ((tags83.drop 16).take 16, (raw83.drop 16).take 16), ((tags83.drop 32).take 16, (raw83.drop 32).take 16), ((tags83.drop 48).take 16, (raw83.drop 48).take 16), ((tags83.drop 64).take 16, (raw83.drop 64).take 16), ((tags83.drop 80).take 16, (raw83.drop 80).take 16), ((tags83.drop 96).take 16, (raw83.drop 96).take 16), ((tags83.drop 112).take 16, (raw83.drop 112).take 16)]

theorem check83 : checkRaw oldMeaning ctrs window terms meaning 20 tags83 raw83 = true := by
  have ht : parts83Refined.flatMap Prod.fst = tags83 := by rfl
  have hr : parts83Refined.flatMap Prod.snd = raw83 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts83Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check83Part0
  · exact check83Part1
  · exact check83Part2
  · exact check83Part3
  · exact check83Part4
  · exact check83Part5
  · exact check83Part6
  · exact check83Part7
end Snake9.LocalWindow.ParallelShare00Applicability
