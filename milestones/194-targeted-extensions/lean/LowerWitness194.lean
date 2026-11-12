import LowerRows194_0
import LowerRows194_1
import LowerRows194_2
import LowerRows194_3
import LowerRows194_4
import LowerRows194_5
import LowerRows194_6
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Lower194
theorem allOldRows (i : Fin 49) : oldRow i := by
  by_cases h0 : i.val < 8
  · have h := oldRows0 ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h1 : i.val < 16
  · have h := oldRows1 ⟨i.val-8,by omega⟩
    have he : (⟨8+(i.val-8),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h2 : i.val < 24
  · have h := oldRows2 ⟨i.val-16,by omega⟩
    have he : (⟨16+(i.val-16),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h3 : i.val < 32
  · have h := oldRows3 ⟨i.val-24,by omega⟩
    have he : (⟨24+(i.val-24),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h4 : i.val < 40
  · have h := oldRows4 ⟨i.val-32,by omega⟩
    have he : (⟨32+(i.val-32),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h5 : i.val < 48
  · have h := oldRows5 ⟨i.val-40,by omega⟩
    have he : (⟨40+(i.val-40),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  have h := oldRows6 ⟨i.val-48,by omega⟩
  have he : (⟨48+(i.val-48),by omega⟩ : Fin 49)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
  simpa only [he] using h
def oldPath : LayerJoining.InducedPath (Fin 128) Adj 48 where
  vertex := oldVertex
  distinct i j h := (allOldRows i j).1 h
  induced i j h := (allOldRows i j).2 h
#print axioms oldPath
theorem allNewRows (i : Fin 50) : newRow i := by
  by_cases h0 : i.val < 8
  · have h := newRows0 ⟨i.val-0,by omega⟩
    have he : (⟨0+(i.val-0),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h1 : i.val < 16
  · have h := newRows1 ⟨i.val-8,by omega⟩
    have he : (⟨8+(i.val-8),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h2 : i.val < 24
  · have h := newRows2 ⟨i.val-16,by omega⟩
    have he : (⟨16+(i.val-16),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h3 : i.val < 32
  · have h := newRows3 ⟨i.val-24,by omega⟩
    have he : (⟨24+(i.val-24),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h4 : i.val < 40
  · have h := newRows4 ⟨i.val-32,by omega⟩
    have he : (⟨32+(i.val-32),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  by_cases h5 : i.val < 48
  · have h := newRows5 ⟨i.val-40,by omega⟩
    have he : (⟨40+(i.val-40),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simpa only [he] using h
  have h := newRows6 ⟨i.val-48,by omega⟩
  have he : (⟨48+(i.val-48),by omega⟩ : Fin 50)=i := by apply Fin.ext; simp only [Fin.val_mk]; omega
  simpa only [he] using h
def newPath : LayerJoining.InducedPath (Fin 128) Adj 49 where
  vertex := newVertex
  distinct i j h := (allNewRows i j).1 h
  induced i j h := (allNewRows i j).2 h
#print axioms newPath
end Lower194
