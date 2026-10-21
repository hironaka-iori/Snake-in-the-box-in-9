import ParallelShareApplicability.ParallelShare00.Check78Part0
import ParallelShareApplicability.ParallelShare00.Check78Part1
import ParallelShareApplicability.ParallelShare00.Check78Part2
import ParallelShareApplicability.ParallelShare00.Check78Part3
import ParallelShareApplicability.ParallelShare00.Check78Part4
import ParallelShareApplicability.ParallelShare00.Check78Part5
import ParallelShareApplicability.ParallelShare00.Check78Part6
import ParallelShareApplicability.ParallelShare00.Check78Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts78Refined : List (List Tag × List (List Nat)) := [((tags78.drop 0).take 16, (raw78.drop 0).take 16), ((tags78.drop 16).take 16, (raw78.drop 16).take 16), ((tags78.drop 32).take 16, (raw78.drop 32).take 16), ((tags78.drop 48).take 16, (raw78.drop 48).take 16), ((tags78.drop 64).take 16, (raw78.drop 64).take 16), ((tags78.drop 80).take 16, (raw78.drop 80).take 16), ((tags78.drop 96).take 16, (raw78.drop 96).take 16), ((tags78.drop 112).take 16, (raw78.drop 112).take 16)]

theorem check78 : checkRaw oldMeaning ctrs window terms meaning 20 tags78 raw78 = true := by
  have ht : parts78Refined.flatMap Prod.fst = tags78 := by rfl
  have hr : parts78Refined.flatMap Prod.snd = raw78 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts78Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check78Part0
  · exact check78Part1
  · exact check78Part2
  · exact check78Part3
  · exact check78Part4
  · exact check78Part5
  · exact check78Part6
  · exact check78Part7
end Snake9.LocalWindow.ParallelShare00Applicability
