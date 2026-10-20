import W2423BG1C0
import W2423BG1C1
import W2423BG1C2
import W2423BG1C3
import W2423BG1C4
import W2423BG1C5
import W2423BG1C6
import W2423BG1C7
import W2423BMain
namespace W2423B
open WinCNF W223G1
theorem check_T : F.all (check T) = true := by
  simp only [F, List.all_append, chk0, chk1, chk2, chk3, chk4, chk5, chk6, chk7, chk8, chk9, chk10, chk11, chk12, chk13, chk14, chk15, chk16, chk17, chk18, chk19, chk20, chk21, chk22, chk23, chk24, chk25, chk26, chk27, chk28, chk29, chk30, chk31, chk32, chk33, chk34, chk35, chk36, chk37, chk38, chk39, chk40, chk41, chk42, chk43, chk44, chk45, chk46, chk47, chk48, chk49, chk50, chk51, chk52, chk53, chk54, chk55, chk56, chk57, Bool.and_self]
theorem refuted : WinG1.Refuted4 3 0 2 2 4 4 2 2 3 3 :=
  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩
end W2423B
