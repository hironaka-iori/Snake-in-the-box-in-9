import HistoryData205
set_option Elab.async false
set_option maxRecDepth 100000
namespace ActivePair205_3_4
open HistoryData205 ActiveTree205
namespace Even
def words : Array Nat := #[0,1,4,32,64,3,129,6,36,68,132,96,160,192,7,35,67,131,133,161,193,38,70,134,100,164,69,196,97,98,162,194,71,163,225,228,226,103,199,167,227,229,230]
def parents : Array Nat := #[0,0,0,0,0,1,1,2,2,2,2,3,3,4,5,5,5,5,6,6,6,7,7,7,8,8,9,9,11,11,12,13,14,15,19,24,29,32,32,33,33,34,35]
def positions : Array Nat := #[0,1,7,29,75,2,36,8,12,96,90,62,28,42,3,33,79,35,91,67,43,9,97,89,15,27,95,85,63,59,69,41,80,34,50,54,58,19,81,23,47,51,55]
def cover : Array Nat := #[0,1,5,14,0,0,0,2,7,21,0,21,8,0,0,24,0,0,0,37,0,0,0,39,0,0,0,25,12,3,0,0,0,15,33,17,6,0,0,0,0,31,13,20,0,0,0,40,0,0,34,41,0,41,35,42,0,42,36,29,0,29,11,28,0,0,0,19,12,30,0,0,0,0,0,4,0,0,0,16,32,38,0,0,0,27,0,0,0,23,10,18,0,0,0,26,9,22,0]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 3) (x.testBit 4)) == false
def base (x : Nat) : Nat := x &&& 231
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 43 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 43 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 43 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 43 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 43 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 43 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 43 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 43 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 43 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 43 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 43 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 43 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 43 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 43 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk32 : ∀ i : Fin 8, positions[(32+i.val)]! < 99 ∧ active seed[positions[(32+i.val)]!]! = true ∧ words[(32+i.val)]! = base seed[positions[(32+i.val)]!]! ∧ (0<(32+i.val) → parents[(32+i.val)]! < (32+i.val) ∧ adjacent words[parents[(32+i.val)]!]! words[(32+i.val)]!) := by decide +kernel
theorem parentFactsChunk40 : ∀ i : Fin 3, positions[(40+i.val)]! < 99 ∧ active seed[positions[(40+i.val)]!]! = true ∧ words[(40+i.val)]! = base seed[positions[(40+i.val)]!]! ∧ (0<(40+i.val) → parents[(40+i.val)]! < (40+i.val) ∧ adjacent words[parents[(40+i.val)]!]! words[(40+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 43, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  by_cases h32 : i.val < 40
  · have hj : i.val-32 < 8 := by omega
    have he : 32+(i.val-32)=i.val := by omega
    have h := parentFactsChunk32 ⟨i.val-32,hj⟩
    simpa only [he] using h
  have hj : i.val-40 < 3 := by omega
  have he : 40+(i.val-40)=i.val := by omega
  have h := parentFactsChunk40 ⟨i.val-40,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 43 Selected adjacent f
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
def words : Array Nat := #[2,34,66,130,35,32,38,98,162,67,64,70,194,128,134,33,39,36,65,195,198,129,97,161,7,103,167,4,100,164,69,193,199,227,196,230,133,101,225,165,5,197,229]
def parents : Array Nat := #[0,0,0,0,1,1,1,1,1,2,2,2,2,3,3,4,4,5,9,9,11,13,15,15,16,16,16,17,17,17,18,18,19,19,20,20,21,22,22,23,24,30,37]
def positions : Array Nat := #[72,71,73,39,32,30,10,60,70,78,74,98,40,38,88,31,21,13,77,45,87,37,64,66,4,18,22,6,14,26,94,44,82,46,84,56,92,17,49,25,5,83,52]
def cover : Array Nat := #[0,0,0,0,24,40,27,0,0,0,6,0,0,17,28,0,28,37,25,0,25,16,26,0,26,39,29,0,0,0,5,15,4,0,0,0,0,21,13,3,12,0,0,0,31,19,33,0,33,38,0,0,42,0,0,0,35,0,0,0,7,0,0,0,22,15,23,0,0,0,8,1,0,2,10,0,10,18,9,0,0,0,32,41,34,0,34,20,14,0,0,0,36,40,30,0,0,0,11]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 3) (x.testBit 4)) == true
def base (x : Nat) : Nat := x &&& 231
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 43 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 43 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 43 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 43 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 43 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 43 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 43 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 43 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 43 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 43 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 43 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 43 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 43 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 43 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk32 : ∀ i : Fin 8, positions[(32+i.val)]! < 99 ∧ active seed[positions[(32+i.val)]!]! = true ∧ words[(32+i.val)]! = base seed[positions[(32+i.val)]!]! ∧ (0<(32+i.val) → parents[(32+i.val)]! < (32+i.val) ∧ adjacent words[parents[(32+i.val)]!]! words[(32+i.val)]!) := by decide +kernel
theorem parentFactsChunk40 : ∀ i : Fin 3, positions[(40+i.val)]! < 99 ∧ active seed[positions[(40+i.val)]!]! = true ∧ words[(40+i.val)]! = base seed[positions[(40+i.val)]!]! ∧ (0<(40+i.val) → parents[(40+i.val)]! < (40+i.val) ∧ adjacent words[parents[(40+i.val)]!]! words[(40+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 43, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  by_cases h32 : i.val < 40
  · have hj : i.val-32 < 8 := by omega
    have he : 32+(i.val-32)=i.val := by omega
    have h := parentFactsChunk32 ⟨i.val-32,hj⟩
    simpa only [he] using h
  have hj : i.val-40 < 3 := by omega
  have he : 40+(i.val-40)=i.val := by omega
  have h := parentFactsChunk40 ⟨i.val-40,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 43 Selected adjacent f
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
end ActivePair205_3_4
