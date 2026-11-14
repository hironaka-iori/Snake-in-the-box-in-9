import HistoryData205
set_option Elab.async false
set_option maxRecDepth 100000
namespace ActivePair205_2_3
open HistoryData205 ActiveTree205
namespace Even
def words : Array Nat := #[0,1,16,3,18,80,50,82,112,208,34,178,83,66,113,96,209,192,98,162,176,242,211,194,97,49,241,193,99,226,163,160,177,243,195,227,161]
def parents : Array Nat := #[0,0,0,1,2,2,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,13,14,14,14,16,18,18,19,19,20,21,22,28,30]
def positions : Array Nat := #[0,1,7,2,8,74,9,73,15,85,10,70,80,98,64,16,44,42,61,69,27,57,45,41,17,65,51,43,18,56,24,26,66,46,82,47,25]
def cover : Array Nat := #[0,1,3,0,3,1,0,2,4,6,10,0,0,0,0,8,15,24,28,0,0,0,0,0,30,36,31,20,0,0,0,0,0,0,0,0,0,0,0,0,0,23,17,27,16,22,33,35,0,0,0,26,0,0,0,0,29,21,0,0,0,18,15,24,14,25,32,36,31,19,11,6,4,7,5,0,0,0,0,0,12,22,34,27,17,9,0,0,0,0,0,0,0,0,0,0,0,0,13]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 2) (x.testBit 3)) == false
def base (x : Nat) : Nat := x &&& 243
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 37 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 37 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 37 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 37 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 37 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 37 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 37 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 37 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 37 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 37 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 37 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 37 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 37 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 37 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk32 : ∀ i : Fin 5, positions[(32+i.val)]! < 99 ∧ active seed[positions[(32+i.val)]!]! = true ∧ words[(32+i.val)]! = base seed[positions[(32+i.val)]!]! ∧ (0<(32+i.val) → parents[(32+i.val)]! < (32+i.val) ∧ adjacent words[parents[(32+i.val)]!]! words[(32+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 37, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  have hj : i.val-32 < 5 := by omega
  have he : 32+(i.val-32)=i.val := by omega
  have h := parentFactsChunk32 ⟨i.val-32,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 37 Selected adjacent f
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
def words : Array Nat := #[3,35,67,34,33,51,99,163,66,65,83,32,98,115,179,227,64,194,81,48,114,226,147,225,80,210,130,17,112,176,242,224,146,145,241,208,128,129]
def parents : Array Nat := #[0,0,0,1,1,1,1,1,2,2,2,3,3,5,5,6,8,8,9,11,12,12,14,15,16,17,17,18,19,19,20,21,22,22,23,24,26,33]
def positions : Array Nat := #[3,32,78,11,31,21,19,23,97,77,79,12,60,20,22,48,76,40,94,13,59,55,35,49,75,87,39,93,14,28,58,54,88,36,50,86,38,37]
def cover : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,3,11,19,28,0,0,0,0,6,13,5,14,7,0,0,0,0,29,19,11,4,1,5,14,22,33,37,36,26,17,0,0,0,0,0,0,0,15,23,34,0,34,23,31,21,0,0,30,20,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,16,9,2,10,0,0,0,0,0,0,35,25,32,26,36,37,33,27,18,9,16,8,0]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 2) (x.testBit 3)) == true
def base (x : Nat) : Nat := x &&& 243
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 38 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 38 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 38 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 38 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 38 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 38 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 38 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 38 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 38 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 38 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 38 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 38 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 38 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 38 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk32 : ∀ i : Fin 6, positions[(32+i.val)]! < 99 ∧ active seed[positions[(32+i.val)]!]! = true ∧ words[(32+i.val)]! = base seed[positions[(32+i.val)]!]! ∧ (0<(32+i.val) → parents[(32+i.val)]! < (32+i.val) ∧ adjacent words[parents[(32+i.val)]!]! words[(32+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 38, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  have hj : i.val-32 < 6 := by omega
  have he : 32+(i.val-32)=i.val := by omega
  have h := parentFactsChunk32 ⟨i.val-32,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 38 Selected adjacent f
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
end ActivePair205_2_3
