import HistoryData205
set_option Elab.async false
set_option maxRecDepth 100000
namespace ActivePair205_1_5
open HistoryData205 ActiveTree205
namespace Even
def words : Array Nat := #[0,1,4,16,64,128,9,12,68,132,80,144,72,192,136,13,25,73,137,28,69,196,133,88,193,77,141,153,201,85,204,212,149,216,209,205,21,220]
def parents : Array Nat := #[0,0,0,0,0,0,1,2,2,2,3,3,4,4,5,6,6,6,6,7,8,8,9,10,13,15,15,16,17,20,21,21,22,23,24,25,29,30]
def positions : Array Nat := #[0,1,11,71,61,69,32,6,96,90,74,70,60,42,38,5,33,77,37,7,19,55,23,59,43,18,24,34,48,20,56,86,22,58,44,83,21,57]
def cover : Array Nat := #[0,1,0,0,0,15,7,19,0,19,7,2,0,0,0,0,0,0,25,20,29,36,32,22,26,0,0,0,0,0,0,0,6,16,27,0,27,18,14,0,0,0,13,24,34,0,34,24,28,0,0,0,0,0,0,21,30,37,33,23,12,4,0,0,0,0,0,0,0,5,11,3,0,0,10,23,12,17,0,0,0,0,0,35,30,37,31,0,0,0,9,22,32,36,29,20,8,0,0]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 1) (x.testBit 5)) == false
def base (x : Nat) : Nat := x &&& 221
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
end Even
namespace Odd
def words : Array Nat := #[1,5,9,17,65,129,4,13,8,73,16,81,145,64,128,20,68,132,77,141,24,136,89,201,80,209,153,192,28,84,148,76,196,140,93,205,152,200,217,213,92,156,212,197,221]
def parents : Array Nat := #[0,0,0,0,0,0,1,1,2,2,3,3,3,4,5,6,6,6,7,7,8,8,9,9,10,11,12,13,15,15,15,16,16,17,18,18,20,21,22,25,28,28,29,32,34]
def positions : Array Nat := #[2,3,31,65,63,67,12,4,30,78,72,64,66,62,68,13,97,89,17,25,29,39,79,49,73,45,35,41,8,14,88,16,54,26,80,82,28,40,50,52,15,27,87,53,51]
def cover : Array Nat := #[0,0,0,1,7,0,0,0,28,0,0,0,6,15,29,40,31,18,0,0,0,0,0,0,0,19,33,41,36,20,8,2,0,0,0,26,0,0,0,21,37,27,0,0,0,25,0,0,0,23,38,44,39,43,32,0,0,0,0,0,0,0,13,4,11,3,12,5,14,0,0,0,10,24,0,0,0,0,9,22,34,44,35,0,0,0,0,42,30,17,0,0,0,0,0,0,0,16,31]
def active (x : Nat) : Bool := (Bool.xor (x.testBit 1) (x.testBit 5)) == true
def base (x : Nat) : Nat := x &&& 221
def Selected (x : Nat) : Prop := ∃ i : Fin 99, active seed[i.val]! = true ∧ base seed[i.val]! = x
theorem coverageChunk0 : ∀ i : Fin 8, active seed[(0+i.val)]! = true → cover[(0+i.val)]! < 45 ∧ words[cover[(0+i.val)]!]! = base seed[(0+i.val)]! := by decide +kernel
theorem coverageChunk8 : ∀ i : Fin 8, active seed[(8+i.val)]! = true → cover[(8+i.val)]! < 45 ∧ words[cover[(8+i.val)]!]! = base seed[(8+i.val)]! := by decide +kernel
theorem coverageChunk16 : ∀ i : Fin 8, active seed[(16+i.val)]! = true → cover[(16+i.val)]! < 45 ∧ words[cover[(16+i.val)]!]! = base seed[(16+i.val)]! := by decide +kernel
theorem coverageChunk24 : ∀ i : Fin 8, active seed[(24+i.val)]! = true → cover[(24+i.val)]! < 45 ∧ words[cover[(24+i.val)]!]! = base seed[(24+i.val)]! := by decide +kernel
theorem coverageChunk32 : ∀ i : Fin 8, active seed[(32+i.val)]! = true → cover[(32+i.val)]! < 45 ∧ words[cover[(32+i.val)]!]! = base seed[(32+i.val)]! := by decide +kernel
theorem coverageChunk40 : ∀ i : Fin 8, active seed[(40+i.val)]! = true → cover[(40+i.val)]! < 45 ∧ words[cover[(40+i.val)]!]! = base seed[(40+i.val)]! := by decide +kernel
theorem coverageChunk48 : ∀ i : Fin 8, active seed[(48+i.val)]! = true → cover[(48+i.val)]! < 45 ∧ words[cover[(48+i.val)]!]! = base seed[(48+i.val)]! := by decide +kernel
theorem coverageChunk56 : ∀ i : Fin 8, active seed[(56+i.val)]! = true → cover[(56+i.val)]! < 45 ∧ words[cover[(56+i.val)]!]! = base seed[(56+i.val)]! := by decide +kernel
theorem coverageChunk64 : ∀ i : Fin 8, active seed[(64+i.val)]! = true → cover[(64+i.val)]! < 45 ∧ words[cover[(64+i.val)]!]! = base seed[(64+i.val)]! := by decide +kernel
theorem coverageChunk72 : ∀ i : Fin 8, active seed[(72+i.val)]! = true → cover[(72+i.val)]! < 45 ∧ words[cover[(72+i.val)]!]! = base seed[(72+i.val)]! := by decide +kernel
theorem coverageChunk80 : ∀ i : Fin 8, active seed[(80+i.val)]! = true → cover[(80+i.val)]! < 45 ∧ words[cover[(80+i.val)]!]! = base seed[(80+i.val)]! := by decide +kernel
theorem coverageChunk88 : ∀ i : Fin 8, active seed[(88+i.val)]! = true → cover[(88+i.val)]! < 45 ∧ words[cover[(88+i.val)]!]! = base seed[(88+i.val)]! := by decide +kernel
theorem coverageChunk96 : ∀ i : Fin 3, active seed[(96+i.val)]! = true → cover[(96+i.val)]! < 45 ∧ words[cover[(96+i.val)]!]! = base seed[(96+i.val)]! := by decide +kernel
theorem coverage : ∀ i : Fin 99, active seed[i.val]! = true → cover[i.val]! < 45 ∧ words[cover[i.val]!]! = base seed[i.val]! := by
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
theorem parentFactsChunk40 : ∀ i : Fin 5, positions[(40+i.val)]! < 99 ∧ active seed[positions[(40+i.val)]!]! = true ∧ words[(40+i.val)]! = base seed[positions[(40+i.val)]!]! ∧ (0<(40+i.val) → parents[(40+i.val)]! < (40+i.val) ∧ adjacent words[parents[(40+i.val)]!]! words[(40+i.val)]!) := by decide +kernel
theorem parentFacts : ∀ i : Fin 45, positions[i.val]! < 99 ∧ active seed[positions[i.val]!]! = true ∧ words[i.val]! = base seed[positions[i.val]!]! ∧ (0<i.val → parents[i.val]! < i.val ∧ adjacent words[parents[i.val]!]! words[i.val]!) := by
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
  have hj : i.val-40 < 5 := by omega
  have he : 40+(i.val-40)=i.val := by omega
  have h := parentFactsChunk40 ⟨i.val-40,hj⟩
  simpa only [he] using h
theorem constantOnActive {W : Type} (f : Nat → W)
    (same : ∀ x y, Selected x → Selected y → adjacent x y → f x=f y) :
    ∀ x, Selected x → f x=f words[0]! := by
  apply coveredConstant (fun i => words[i]!) (fun i => parents[i]!) 45 Selected adjacent f
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
end ActivePair205_1_5
