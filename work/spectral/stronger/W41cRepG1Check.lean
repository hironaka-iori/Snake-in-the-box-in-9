import W41cRepG1C0
import W41cRepMain
namespace W41cRep
open WinCNF W223G1
theorem check_T : F.all (check T) = true := by
  simp only [F, List.all_append, chk0, chk1, chk2, chk3, chk4, chk5, Bool.and_self]
theorem refuted : WinG1.Refuted3 0 4 4 1 1 4 6 :=
  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩
end W41cRep
