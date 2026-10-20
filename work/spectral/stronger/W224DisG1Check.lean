import W224DisG1C0
import W224DisG1C1
import W224DisG1C2
import W224DisG1C3
import W224DisG1C4
import W224DisG1C5
import W224DisMain
namespace W224Dis
open WinCNF W223G1
theorem check_T : F.all (check T) = true := by
  simp only [F, List.all_append, chk0, chk1, chk2, chk3, chk4, chk5, chk6, chk7, chk8, chk9, chk10, chk11, chk12, chk13, chk14, chk15, chk16, chk17, chk18, chk19, chk20, chk21, chk22, chk23, chk24, chk25, chk26, chk27, chk28, chk29, chk30, chk31, chk32, chk33, chk34, chk35, chk36, chk37, chk38, chk39, chk40, chk41, chk42, chk43, chk44, chk45, chk46, chk47, Bool.and_self]
theorem refuted : WinG1.Refuted3 3 2 2 2 2 4 4 :=
  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩
end W224Dis
