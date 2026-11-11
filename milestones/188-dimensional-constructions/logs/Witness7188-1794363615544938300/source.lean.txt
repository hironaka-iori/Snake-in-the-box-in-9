import CubeRows7_00188
import CubeRows7_01188
import CubeRows7_02188
import CubeRows7_03188
import CubeRows7_04188
import CubeRows7_05188
import CubeRows7_06188
namespace Dimensional188.Witness7
theorem allRows (i : Fin 51) : Row i := by
  by_cases h0 : i.val < 8
  · have h := rows0 ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h1 : i.val < 16
  · have h := rows1 ⟨i.val-8,by omega⟩
    have he : (⟨8+(i.val-8),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h2 : i.val < 24
  · have h := rows2 ⟨i.val-16,by omega⟩
    have he : (⟨16+(i.val-16),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h3 : i.val < 32
  · have h := rows3 ⟨i.val-24,by omega⟩
    have he : (⟨24+(i.val-24),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h4 : i.val < 40
  · have h := rows4 ⟨i.val-32,by omega⟩
    have he : (⟨32+(i.val-32),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h5 : i.val < 48
  · have h := rows5 ⟨i.val-40,by omega⟩
    have he : (⟨40+(i.val-40),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  have h := rows6 ⟨i.val-48,by omega⟩
  have he : (⟨48+(i.val-48),by omega⟩ : Fin 51)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
  simpa only [he] using h
theorem path_distinct : ∀ i j, pathVertex i = pathVertex j → i=j := by
  intro i j h
  exact (allRows i j).1 h
theorem path_induced : ∀ i j, i.val < j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val) := by
  intro i j h
  exact (allRows i j).2 h
def path : LayerJoining.InducedPath (Fin 128) Adj 50 := ⟨pathVertex,path_distinct,path_induced⟩
#print axioms allRows
#print axioms path_distinct
#print axioms path_induced
end Dimensional188.Witness7
