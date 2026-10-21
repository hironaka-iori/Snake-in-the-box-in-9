import ParallelShareApplicability.ParallelShare00.Check73Part0
import ParallelShareApplicability.ParallelShare00.Check73Part1
import ParallelShareApplicability.ParallelShare00.Check73Part2
import ParallelShareApplicability.ParallelShare00.Check73Part3
import ParallelShareApplicability.ParallelShare00.Check73Part4
import ParallelShareApplicability.ParallelShare00.Check73Part5
import ParallelShareApplicability.ParallelShare00.Check73Part6
import ParallelShareApplicability.ParallelShare00.Check73Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts73Refined : List (List Tag × List (List Nat)) := [((tags73.drop 0).take 16, (raw73.drop 0).take 16), ((tags73.drop 16).take 16, (raw73.drop 16).take 16), ((tags73.drop 32).take 16, (raw73.drop 32).take 16), ((tags73.drop 48).take 16, (raw73.drop 48).take 16), ((tags73.drop 64).take 16, (raw73.drop 64).take 16), ((tags73.drop 80).take 16, (raw73.drop 80).take 16), ((tags73.drop 96).take 16, (raw73.drop 96).take 16), ((tags73.drop 112).take 16, (raw73.drop 112).take 16)]

theorem check73 : checkRaw oldMeaning ctrs window terms meaning 20 tags73 raw73 = true := by
  have ht : parts73Refined.flatMap Prod.fst = tags73 := by rfl
  have hr : parts73Refined.flatMap Prod.snd = raw73 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts73Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check73Part0
  · exact check73Part1
  · exact check73Part2
  · exact check73Part3
  · exact check73Part4
  · exact check73Part5
  · exact check73Part6
  · exact check73Part7
end Snake9.LocalWindow.ParallelShare00Applicability
