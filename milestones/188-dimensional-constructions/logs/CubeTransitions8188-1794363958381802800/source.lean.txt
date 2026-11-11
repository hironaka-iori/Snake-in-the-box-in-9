import CubeSteps8_00188
import CubeSteps8_01188
import CubeSteps8_02188
import CubeSteps8_03188
import CubeSteps8_04188
import CubeSteps8_05188
import CubeSteps8_06188
import CubeSteps8_07188
import CubeSteps8_08188
import CubeSteps8_09188
import CubeSteps8_10188
import CubeSteps8_11188
import CubeSteps8_12188
import CubeSteps8_13188
namespace Dimensional188.Witness8
theorem transitions_agree (i : Fin 98) :
  (pathVertex ⟨i.val+1,by omega⟩).val = Nat.xor (pathVertex ⟨i.val,by omega⟩).val (2^transitions[i.val]!) := by
  by_cases h0 : i.val < 7
  · have h := steps0 ⟨i.val-0,by omega⟩
    have he : 0+(i.val-0)=i.val := by omega
    simpa only [he] using h
  by_cases h1 : i.val < 14
  · have h := steps1 ⟨i.val-7,by omega⟩
    have he : 7+(i.val-7)=i.val := by omega
    simpa only [he] using h
  by_cases h2 : i.val < 21
  · have h := steps2 ⟨i.val-14,by omega⟩
    have he : 14+(i.val-14)=i.val := by omega
    simpa only [he] using h
  by_cases h3 : i.val < 28
  · have h := steps3 ⟨i.val-21,by omega⟩
    have he : 21+(i.val-21)=i.val := by omega
    simpa only [he] using h
  by_cases h4 : i.val < 35
  · have h := steps4 ⟨i.val-28,by omega⟩
    have he : 28+(i.val-28)=i.val := by omega
    simpa only [he] using h
  by_cases h5 : i.val < 42
  · have h := steps5 ⟨i.val-35,by omega⟩
    have he : 35+(i.val-35)=i.val := by omega
    simpa only [he] using h
  by_cases h6 : i.val < 49
  · have h := steps6 ⟨i.val-42,by omega⟩
    have he : 42+(i.val-42)=i.val := by omega
    simpa only [he] using h
  by_cases h7 : i.val < 56
  · have h := steps7 ⟨i.val-49,by omega⟩
    have he : 49+(i.val-49)=i.val := by omega
    simpa only [he] using h
  by_cases h8 : i.val < 63
  · have h := steps8 ⟨i.val-56,by omega⟩
    have he : 56+(i.val-56)=i.val := by omega
    simpa only [he] using h
  by_cases h9 : i.val < 70
  · have h := steps9 ⟨i.val-63,by omega⟩
    have he : 63+(i.val-63)=i.val := by omega
    simpa only [he] using h
  by_cases h10 : i.val < 77
  · have h := steps10 ⟨i.val-70,by omega⟩
    have he : 70+(i.val-70)=i.val := by omega
    simpa only [he] using h
  by_cases h11 : i.val < 84
  · have h := steps11 ⟨i.val-77,by omega⟩
    have he : 77+(i.val-77)=i.val := by omega
    simpa only [he] using h
  by_cases h12 : i.val < 91
  · have h := steps12 ⟨i.val-84,by omega⟩
    have he : 84+(i.val-84)=i.val := by omega
    simpa only [he] using h
  have h := steps13 ⟨i.val-91,by omega⟩
  have he : 91+(i.val-91)=i.val := by omega
  simpa only [he] using h
#print axioms transitions_agree
end Dimensional188.Witness8
