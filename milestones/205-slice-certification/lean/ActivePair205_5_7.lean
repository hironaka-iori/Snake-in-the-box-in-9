import HistoryData205
set_option Elab.async false
set_option maxRecDepth 100000
namespace ActivePair205_5_7
open HistoryData205 ActiveTree205
namespace Even
def words : Array Nat := #[0,1,2,3,17,18,7,67,21,82,15,23,75,83,85,80,90,13,73,91,93,69,88,94,12,72,89,95,27,68,24,78,30,28,70]
def parents : Array Nat := #[0,0,0,1,1,2,3,3,4,5,6,6,7,7,8,9,9,10,12,12,14,14,15,16,17,18,18,19,19,21,22,23,23,24,29]
def positions : Array Nat := #[0,1,69,2,66,70,3,47,93,73,4,22,48,46,52,74,58,5,49,79,51,53,75,57,6,76,50,80,34,54,28,56,8,7,55]
def cover : Array Nat := #[0,1,3,6,10,17,24,33,32,0,0,0,0,0,0,0,0,0,0,0,0,0,11,6,10,17,24,33,30,0,0,0,0,0,28,0,0,0,0,0,0,0,0,0,0,0,13,7,12,18,26,20,14,21,29,34,31,23,16,0,0,0,0,0,0,0,4,1,0,2,5,0,5,9,15,22,25,18,12,19,27,0,0,0,0,0,0,0,0,0,0,0,0,8,14,21,29,34,31]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 5) (x.testBit 7)) == false
def base (x : Nat) : Nat := x &&& 95
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 35 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 35 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 35 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 35 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 35 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 35 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 35 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 35 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 35 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 35 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 35 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 35 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 35 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 35 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
  intro i
  have hi := i.isLt
  by_cases h0 : i.val < 8
  · have hj : i.val-0 < 8 := by omega
    have he : 0+(i.val-0)=i.val := by omega
    have h := coverageChunk0 ⟨i.val-0,hj⟩
    simpa only [he] using h
  by_cases h8 : i.val < 16
  · have hj : i.val-8 < 8 := by omega
    have he : 8+(i.val-8)=i.val := by omega
    have h := coverageChunk8 ⟨i.val-8,hj⟩
    simpa only [he] using h
  by_cases h16 : i.val < 24
  · have hj : i.val-16 < 8 := by omega
    have he : 16+(i.val-16)=i.val := by omega
    have h := coverageChunk16 ⟨i.val-16,hj⟩
    simpa only [he] using h
  by_cases h24 : i.val < 32
  · have hj : i.val-24 < 8 := by omega
    have he : 24+(i.val-24)=i.val := by omega
    have h := coverageChunk24 ⟨i.val-24,hj⟩
    simpa only [he] using h
  by_cases h32 : i.val < 40
  · have hj : i.val-32 < 8 := by omega
    have he : 32+(i.val-32)=i.val := by omega
    have h := coverageChunk32 ⟨i.val-32,hj⟩
    simpa only [he] using h
  by_cases h40 : i.val < 48
  · have hj : i.val-40 < 8 := by omega
    have he : 40+(i.val-40)=i.val := by omega
    have h := coverageChunk40 ⟨i.val-40,hj⟩
    simpa only [he] using h
  by_cases h48 : i.val < 56
  · have hj : i.val-48 < 8 := by omega
    have he : 48+(i.val-48)=i.val := by omega
    have h := coverageChunk48 ⟨i.val-48,hj⟩
    simpa only [he] using h
  by_cases h56 : i.val < 64
  · have hj : i.val-56 < 8 := by omega
    have he : 56+(i.val-56)=i.val := by omega
    have h := coverageChunk56 ⟨i.val-56,hj⟩
    simpa only [he] using h
  by_cases h64 : i.val < 72
  · have hj : i.val-64 < 8 := by omega
    have he : 64+(i.val-64)=i.val := by omega
    have h := coverageChunk64 ⟨i.val-64,hj⟩
    simpa only [he] using h
  by_cases h72 : i.val < 80
  · have hj : i.val-72 < 8 := by omega
    have he : 72+(i.val-72)=i.val := by omega
    have h := coverageChunk72 ⟨i.val-72,hj⟩
    simpa only [he] using h
  by_cases h80 : i.val < 88
  · have hj : i.val-80 < 8 := by omega
    have he : 80+(i.val-80)=i.val := by omega
    have h := coverageChunk80 ⟨i.val-80,hj⟩
    simpa only [he] using h
  by_cases h88 : i.val < 96
  · have hj : i.val-88 < 8 := by omega
    have he : 88+(i.val-88)=i.val := by omega
    have h := coverageChunk88 ⟨i.val-88,hj⟩
    simpa only [he] using h
  have hj : i.val-96 < 3 := by omega
  have he : 96+(i.val-96)=i.val := by omega
  have h := coverageChunk96 ⟨i.val-96,hj⟩
  simpa only [he] using h
theorem parentFactsChunk0 : ∀ i : Fin 8, positions[(0+i.val)]! < 99 ∧ active seed[positions[(0+i.val)]!]! = true ∧ words[(0+i.val)]! = base seed[positions[(0+i.val)]!]! ∧ (0<(0+i.val) → parents[(0+i.val)]! < (0+i.val) ∧ adjacent words[parents[(0+i.val)]!]! words[(0+i.val)]!) := by decide +kernel
theorem parentFactsChunk8 : ∀ i : Fin 8, positions[(8+i.val)]! < 99 ∧ active seed[positions[(8+i.val)]!]! = true ∧ words[(8+i.val)]! = base seed[positions[(8+i.val)]!]! ∧ (0<(8+i.val) → parents[(8+i.val)]! < (8+i.val) ∧ adjacent words[parents[(8+i.val)]!]! words[(8+i.val)]!) := by decide +kernel
theorem parentFactsChunk16 : ∀ i : Fin 8, positions[(16+i.val)]! < 99 ∧ active seed[positions[(16+i.val)]!]! = true ∧ words[(16+i.val)]! = base seed[positions[(16+i.val)]!]! ∧ (0<(16+i.val) → parents[(16+i.val)]! < (16+i.val) ∧ adjacent words[parents[(16+i.val)]!]! words[(16+i.val)]!) := by decide +kernel
theorem parentFactsChunk24 : ∀ i : Fin 8, positions[(24+i.val)]! < 99 ∧ active seed[positions[(24+i.val)]!]! = true ∧ words[(24+i.val)]! = base seed[positions[(24+i.val)]!]! ∧ (0<(24+i.val) → parents[(24+i.val)]! < (24+i.val) ∧ adjacent words[parents[(24+i.val)]!]! words[(24+i.val)]!) := by decide +kernel
theorem parentFactsChunk32 : ∀ i : Fin 3, positions[(32+i.val)]! < 99 ∧ active seed[positions[(32+i.val)]!]! = true ∧ words[(32+i.val)]! = base seed[positions[(32+i.val)]!]! ∧ (0<(32+i.val) → parents[(32+i.val)]! < (32+i.val) ∧ adjacent words[parents[(32+i.val)]!]! words[(32+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 35, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
  intro i
  have hi := i.isLt
  by_cases h0 : i.val < 8
  · have hj : i.val-0 < 8 := by omega
    have he : 0+(i.val-0)=i.val := by omega
    have h := parentFactsChunk0 ⟨i.val-0,hj⟩
    simpa only [he] using h
  by_cases h8 : i.val < 16
  · have hj : i.val-8 < 8 := by omega
    have he : 8+(i.val-8)=i.val := by omega
    have h := parentFactsChunk8 ⟨i.val-8,hj⟩
    simpa only [he] using h
  by_cases h16 : i.val < 24
  · have hj : i.val-16 < 8 := by omega
    have he : 16+(i.val-16)=i.val := by omega
    have h := parentFactsChunk16 ⟨i.val-16,hj⟩
    simpa only [he] using h
  by_cases h24 : i.val < 32
  · have hj : i.val-24 < 8 := by omega
    have he : 24+(i.val-24)=i.val := by omega
    have h := parentFactsChunk24 ⟨i.val-24,hj⟩
    simpa only [he] using h
  have hj : i.val-32 < 3 := by omega
  have he : 32+(i.val-32)=i.val := by omega
  have h := parentFactsChunk32 ⟨i.val-32,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 35 Selected adjacent f
  · intro j hj
    have h := parentFacts ⟨j,hj⟩
    exact ⟨⟨positions[j]!,h.1⟩,h.2.1,h.2.2.1.symm⟩
  · intro x hx
    rcases hx with ⟨i,ha,hb⟩
    have h := coverage i ha
    exact ⟨cover[i.val]!,h.1,h.2.trans hb⟩
  · intro j hpos hj; exact ((parentFacts ⟨j,hj⟩).2.2.2 hpos).1
  · intro j hpos hj; exact ((parentFacts ⟨j,hj⟩).2.2.2 hpos).2
  · exact same
#print axioms coverage
#print axioms parentFacts
#print axioms constantOnActive
end Even
namespace Odd
def words : Array Nat := #[4,5,6,20,21,14,22,84,23,17,10,30,18,86,92,87,25,81,11,8,74,76,83,95,71,24,27,9,65,66,90,77,79,64]
def parents : Array Nat := #[0,0,0,0,1,2,2,3,4,4,5,5,6,6,7,8,9,9,10,10,10,14,15,15,15,16,16,16,17,20,20,21,23,28]
def positions : Array Nat := #[12,91,11,13,92,10,88,14,21,65,39,9,71,87,15,20,36,44,32,30,40,16,45,81,19,29,33,31,43,41,59,17,18,42]
def cover : Array Nat := #[0,0,0,0,0,0,0,0,0,11,5,2,0,3,7,14,21,31,32,24,15,8,0,0,0,0,0,0,0,25,19,27,18,26,0,26,16,27,19,10,20,29,33,28,17,22,0,0,0,0,0,0,0,0,0,0,0,0,0,30,20,29,33,28,17,9,0,0,0,0,0,12,0,0,0,0,0,0,0,0,0,23,32,31,21,14,7,13,6,2,0,1,4,0,0,0,0,0,0]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 5) (x.testBit 7)) == true
def base (x : Nat) : Nat := x &&& 95
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 34 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 34 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 34 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 34 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 34 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 34 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 34 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 34 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 34 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 34 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 34 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 34 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 34 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 34 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
  intro i
  have hi := i.isLt
  by_cases h0 : i.val < 8
  · have hj : i.val-0 < 8 := by omega
    have he : 0+(i.val-0)=i.val := by omega
    have h := coverageChunk0 ⟨i.val-0,hj⟩
    simpa only [he] using h
  by_cases h8 : i.val < 16
  · have hj : i.val-8 < 8 := by omega
    have he : 8+(i.val-8)=i.val := by omega
    have h := coverageChunk8 ⟨i.val-8,hj⟩
    simpa only [he] using h
  by_cases h16 : i.val < 24
  · have hj : i.val-16 < 8 := by omega
    have he : 16+(i.val-16)=i.val := by omega
    have h := coverageChunk16 ⟨i.val-16,hj⟩
    simpa only [he] using h
  by_cases h24 : i.val < 32
  · have hj : i.val-24 < 8 := by omega
    have he : 24+(i.val-24)=i.val := by omega
    have h := coverageChunk24 ⟨i.val-24,hj⟩
    simpa only [he] using h
  by_cases h32 : i.val < 40
  · have hj : i.val-32 < 8 := by omega
    have he : 32+(i.val-32)=i.val := by omega
    have h := coverageChunk32 ⟨i.val-32,hj⟩
    simpa only [he] using h
  by_cases h40 : i.val < 48
  · have hj : i.val-40 < 8 := by omega
    have he : 40+(i.val-40)=i.val := by omega
    have h := coverageChunk40 ⟨i.val-40,hj⟩
    simpa only [he] using h
  by_cases h48 : i.val < 56
  · have hj : i.val-48 < 8 := by omega
    have he : 48+(i.val-48)=i.val := by omega
    have h := coverageChunk48 ⟨i.val-48,hj⟩
    simpa only [he] using h
  by_cases h56 : i.val < 64
  · have hj : i.val-56 < 8 := by omega
    have he : 56+(i.val-56)=i.val := by omega
    have h := coverageChunk56 ⟨i.val-56,hj⟩
    simpa only [he] using h
  by_cases h64 : i.val < 72
  · have hj : i.val-64 < 8 := by omega
    have he : 64+(i.val-64)=i.val := by omega
    have h := coverageChunk64 ⟨i.val-64,hj⟩
    simpa only [he] using h
  by_cases h72 : i.val < 80
  · have hj : i.val-72 < 8 := by omega
    have he : 72+(i.val-72)=i.val := by omega
    have h := coverageChunk72 ⟨i.val-72,hj⟩
    simpa only [he] using h
  by_cases h80 : i.val < 88
  · have hj : i.val-80 < 8 := by omega
    have he : 80+(i.val-80)=i.val := by omega
    have h := coverageChunk80 ⟨i.val-80,hj⟩
    simpa only [he] using h
  by_cases h88 : i.val < 96
  · have hj : i.val-88 < 8 := by omega
    have he : 88+(i.val-88)=i.val := by omega
    have h := coverageChunk88 ⟨i.val-88,hj⟩
    simpa only [he] using h
  have hj : i.val-96 < 3 := by omega
  have he : 96+(i.val-96)=i.val := by omega
  have h := coverageChunk96 ⟨i.val-96,hj⟩
  simpa only [he] using h
theorem parentFactsChunk0 : ∀ i : Fin 8, positions[(0+i.val)]! < 99 ∧ active seed[positions[(0+i.val)]!]! = true ∧ words[(0+i.val)]! = base seed[positions[(0+i.val)]!]! ∧ (0<(0+i.val) → parents[(0+i.val)]! < (0+i.val) ∧ adjacent words[parents[(0+i.val)]!]! words[(0+i.val)]!) := by decide +kernel
theorem parentFactsChunk8 : ∀ i : Fin 8, positions[(8+i.val)]! < 99 ∧ active seed[positions[(8+i.val)]!]! = true ∧ words[(8+i.val)]! = base seed[positions[(8+i.val)]!]! ∧ (0<(8+i.val) → parents[(8+i.val)]! < (8+i.val) ∧ adjacent words[parents[(8+i.val)]!]! words[(8+i.val)]!) := by decide +kernel
theorem parentFactsChunk16 : ∀ i : Fin 8, positions[(16+i.val)]! < 99 ∧ active seed[positions[(16+i.val)]!]! = true ∧ words[(16+i.val)]! = base seed[positions[(16+i.val)]!]! ∧ (0<(16+i.val) → parents[(16+i.val)]! < (16+i.val) ∧ adjacent words[parents[(16+i.val)]!]! words[(16+i.val)]!) := by decide +kernel
theorem parentFactsChunk24 : ∀ i : Fin 8, positions[(24+i.val)]! < 99 ∧ active seed[positions[(24+i.val)]!]! = true ∧ words[(24+i.val)]! = base seed[positions[(24+i.val)]!]! ∧ (0<(24+i.val) → parents[(24+i.val)]! < (24+i.val) ∧ adjacent words[parents[(24+i.val)]!]! words[(24+i.val)]!) := by decide +kernel
theorem parentFactsChunk32 : ∀ i : Fin 2, positions[(32+i.val)]! < 99 ∧ active seed[positions[(32+i.val)]!]! = true ∧ words[(32+i.val)]! = base seed[positions[(32+i.val)]!]! ∧ (0<(32+i.val) → parents[(32+i.val)]! < (32+i.val) ∧ adjacent words[parents[(32+i.val)]!]! words[(32+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 34, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
  intro i
  have hi := i.isLt
  by_cases h0 : i.val < 8
  · have hj : i.val-0 < 8 := by omega
    have he : 0+(i.val-0)=i.val := by omega
    have h := parentFactsChunk0 ⟨i.val-0,hj⟩
    simpa only [he] using h
  by_cases h8 : i.val < 16
  · have hj : i.val-8 < 8 := by omega
    have he : 8+(i.val-8)=i.val := by omega
    have h := parentFactsChunk8 ⟨i.val-8,hj⟩
    simpa only [he] using h
  by_cases h16 : i.val < 24
  · have hj : i.val-16 < 8 := by omega
    have he : 16+(i.val-16)=i.val := by omega
    have h := parentFactsChunk16 ⟨i.val-16,hj⟩
    simpa only [he] using h
  by_cases h24 : i.val < 32
  · have hj : i.val-24 < 8 := by omega
    have he : 24+(i.val-24)=i.val := by omega
    have h := parentFactsChunk24 ⟨i.val-24,hj⟩
    simpa only [he] using h
  have hj : i.val-32 < 2 := by omega
  have he : 32+(i.val-32)=i.val := by omega
  have h := parentFactsChunk32 ⟨i.val-32,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 34 Selected adjacent f
  · intro j hj
    have h := parentFacts ⟨j,hj⟩
    exact ⟨⟨positions[j]!,h.1⟩,h.2.1,h.2.2.1.symm⟩
  · intro x hx
    rcases hx with ⟨i,ha,hb⟩
    have h := coverage i ha
    exact ⟨cover[i.val]!,h.1,h.2.trans hb⟩
  · intro j hpos hj; exact ((parentFacts ⟨j,hj⟩).2.2.2 hpos).1
  · intro j hpos hj; exact ((parentFacts ⟨j,hj⟩).2.2.2 hpos).2
  · exact same
#print axioms coverage
#print axioms parentFacts
#print axioms constantOnActive
end Odd
end ActivePair205_5_7
