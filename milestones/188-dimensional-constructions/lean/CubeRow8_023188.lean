import CubeData8188
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Dimensional188.Witness8
theorem row23part0 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨0+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part1 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨11+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part2 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨22+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part3 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨33+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part4 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨44+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part5 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨55+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part6 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨66+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part7 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨77+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23part8 : ∀ t : Fin 11,
          let j : Fin 99 := ⟨88+t.val,by omega⟩
          let i : Fin 99 := ⟨23,by omega⟩
          (pathVertex i = pathVertex j → i=j) ∧
          (i.val<j.val → (Adj (pathVertex i) (pathVertex j) ↔ i.val+1=j.val)) := by decide +kernel
theorem row23 : Row ⟨23,by omega⟩ := by
  intro j
  by_cases h0 : j.val < 11
  · have h := row23part0 ⟨j.val-0,by omega⟩
    have he : (⟨0+(j.val-0),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h1 : j.val < 22
  · have h := row23part1 ⟨j.val-11,by omega⟩
    have he : (⟨11+(j.val-11),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h2 : j.val < 33
  · have h := row23part2 ⟨j.val-22,by omega⟩
    have he : (⟨22+(j.val-22),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h3 : j.val < 44
  · have h := row23part3 ⟨j.val-33,by omega⟩
    have he : (⟨33+(j.val-33),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h4 : j.val < 55
  · have h := row23part4 ⟨j.val-44,by omega⟩
    have he : (⟨44+(j.val-44),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h5 : j.val < 66
  · have h := row23part5 ⟨j.val-55,by omega⟩
    have he : (⟨55+(j.val-55),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h6 : j.val < 77
  · have h := row23part6 ⟨j.val-66,by omega⟩
    have he : (⟨66+(j.val-66),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  by_cases h7 : j.val < 88
  · have h := row23part7 ⟨j.val-77,by omega⟩
    have he : (⟨77+(j.val-77),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
    simp only at h
    simpa only [he] using h
  have h := row23part8 ⟨j.val-88,by omega⟩
  have he : (⟨88+(j.val-88),by omega⟩ : Fin 99)=j := by apply Fin.ext; simp only [Fin.val_mk]; omega
  simp only at h
  simpa only [he] using h
#print axioms row23
end Dimensional188.Witness8
