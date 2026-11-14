import HistoryData205
set_option Elab.async false
set_option maxRecDepth 100000
namespace ActivePair205_1_6
open HistoryData205 ActiveTree205
namespace Even
def words : Array Nat := #[0,1,4,16,32,128,9,12,36,132,40,160,136,13,25,41,137,28,37,52,164,133,148,56,161,29,45,141,153,169,53,172,149,184,177,21,157,173,145,49,188]
def parents : Array Nat := #[0,0,0,0,0,0,1,2,2,2,4,4,5,6,6,6,6,7,8,8,8,9,9,10,11,13,13,13,14,15,18,20,21,23,24,25,25,26,28,30,31]
def positions : Array Nat := #[0,1,97,73,61,41,78,6,12,90,30,68,38,5,79,31,37,7,19,13,55,91,87,29,47,80,18,82,36,48,20,26,92,28,46,93,81,25,45,65,27]
def cover : Array Nat := #[0,1,0,0,0,13,7,17,0,0,0,0,8,19,0,0,0,0,26,18,30,0,0,0,0,37,31,40,33,23,10,15,0,0,0,0,28,16,12,0,12,5,0,0,0,38,34,24,29,0,0,0,0,0,0,20,31,40,33,23,10,4,0,0,0,39,34,24,11,0,0,0,0,3,0,0,0,0,6,14,25,36,27,0,0,0,0,22,0,0,9,21,32,35,0,0,0,2,7]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 1) (x.testBit 6)) == false
def base (x : Nat) : Nat := x &&& 189
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 41 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 41 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 41 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 41 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 41 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 41 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 41 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 41 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 41 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 41 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 41 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 41 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 41 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 41 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk40 : ∀ i : Fin 1, positions[(40+i.val)]! < 99 ∧ active seed[positions[(40+i.val)]!]! = true ∧ words[(40+i.val)]! = base seed[positions[(40+i.val)]!]! ∧ (0<(40+i.val) → parents[(40+i.val)]! < (40+i.val) ∧ adjacent words[parents[(40+i.val)]!]! words[(40+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 41, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  have hj : i.val-40 < 1 := by omega
  have he : 40+(i.val-40)=i.val := by omega
  have h := parentFactsChunk40 ⟨i.val-40,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 41 Selected adjacent f
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
def words : Array Nat := #[1,5,9,33,129,4,13,21,8,41,32,49,128,145,36,132,45,141,53,24,136,57,169,48,160,153,44,52,164,140,148,173,181,28,16,185,176,60,165,156,189]
def parents : Array Nat := #[0,0,0,0,0,1,1,1,2,2,3,3,4,4,5,5,6,6,7,8,8,9,9,10,10,13,14,14,14,15,15,16,18,19,19,21,23,26,28,29,31]
def positions : Array Nat := #[2,3,77,63,43,96,4,94,76,32,62,64,42,44,11,89,17,83,21,75,39,33,49,71,69,35,10,14,54,84,86,24,22,8,72,34,70,9,23,85,51]
def cover : Array Nat := #[0,0,0,1,6,0,0,0,33,37,26,14,0,0,27,37,26,16,0,0,0,18,32,38,31,0,0,0,0,0,0,0,9,21,35,25,0,0,0,20,0,0,12,4,13,0,0,0,0,22,35,40,32,38,28,0,0,0,0,0,0,0,10,3,11,0,0,0,0,24,36,23,34,0,34,19,8,2,0,0,0,0,0,17,29,39,30,0,30,15,0,0,0,0,7,1,5,0,0]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 1) (x.testBit 6)) == true
def base (x : Nat) : Nat := x &&& 189
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 41 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 41 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 41 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 41 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 41 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 41 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 41 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 41 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 41 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 41 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 41 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 41 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 41 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 41 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk40 : ∀ i : Fin 1, positions[(40+i.val)]! < 99 ∧ active seed[positions[(40+i.val)]!]! = true ∧ words[(40+i.val)]! = base seed[positions[(40+i.val)]!]! ∧ (0<(40+i.val) → parents[(40+i.val)]! < (40+i.val) ∧ adjacent words[parents[(40+i.val)]!]! words[(40+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 41, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  have hj : i.val-40 < 1 := by omega
  have he : 40+(i.val-40)=i.val := by omega
  have h := parentFactsChunk40 ⟨i.val-40,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 41 Selected adjacent f
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
end ActivePair205_1_6
