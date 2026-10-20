import W3242AG1C0
import W3242AG1C1
import W3242AG1C2
import W3242AMain
namespace W3242A
open WinCNF W223G1
theorem check_T : F.all (check T) = true := by
  simp only [F, List.all_append, chk0, chk1, chk2, chk3, chk4, chk5, chk6, chk7, chk8, chk9, chk10, chk11, chk12, chk13, chk14, chk15, chk16, chk17, chk18, Bool.and_self]
theorem refuted : WinG1.Refuted4 0 3 3 3 2 2 4 4 2 2 :=
  ⟨T, F, unsatF, blocksOK_T, check_T, by decide +kernel, by decide⟩
end W3242A
