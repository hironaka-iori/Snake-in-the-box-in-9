import ParallelShareApplicability.ParallelShare00.Check47Part0
import ParallelShareApplicability.ParallelShare00.Check47Part1
import ParallelShareApplicability.ParallelShare00.Check47Part2
import ParallelShareApplicability.ParallelShare00.Check47Part3
import ParallelShareApplicability.ParallelShare00.Check47Part4
import ParallelShareApplicability.ParallelShare00.Check47Part5
import ParallelShareApplicability.ParallelShare00.Check47Part6
import ParallelShareApplicability.ParallelShare00.Check47Part7
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.ParallelShare00Applicability
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate

def parts47Refined : List (List Tag × List (List Nat)) := [((tags47.drop 0).take 16, (raw47.drop 0).take 16), ((tags47.drop 16).take 16, (raw47.drop 16).take 16), ((tags47.drop 32).take 16, (raw47.drop 32).take 16), ((tags47.drop 48).take 16, (raw47.drop 48).take 16), ((tags47.drop 64).take 16, (raw47.drop 64).take 16), ((tags47.drop 80).take 16, (raw47.drop 80).take 16), ((tags47.drop 96).take 16, (raw47.drop 96).take 16), ((tags47.drop 112).take 16, (raw47.drop 112).take 16)]

theorem check47 : checkRaw oldMeaning ctrs window terms meaning 20 tags47 raw47 = true := by
  have ht : parts47Refined.flatMap Prod.fst = tags47 := by rfl
  have hr : parts47Refined.flatMap Prod.snd = raw47 := by rfl
  rw [← ht, ← hr]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts47Refined, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact check47Part0
  · exact check47Part1
  · exact check47Part2
  · exact check47Part3
  · exact check47Part4
  · exact check47Part5
  · exact check47Part6
  · exact check47Part7
end Snake9.LocalWindow.ParallelShare00Applicability
