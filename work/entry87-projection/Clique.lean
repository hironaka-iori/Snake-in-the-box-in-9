import Std

namespace Entry87

/-- A list of distinct elements drawn from a finite supply has length at most that supply. -/
theorem capacity {α : Type} [DecidableEq α] {xs : List α} (distinct : xs.Nodup)
    (supply : List α) (covered : ∀ x ∈ xs, x ∈ supply) : xs.length ≤ supply.length := by
  induction xs generalizing supply with
  | nil => simp
  | cons h tail ih =>
    obtain ⟨fresh, nodup⟩ := List.nodup_cons.mp distinct
    have present : h ∈ supply := covered h (by simp)
    have smaller := ih nodup (supply.erase h) (by
      intro x hx
      have ne : x ≠ h := by intro eq; exact fresh (eq ▸ hx)
      exact (List.mem_erase_of_ne ne).mpr (covered x (by simp [hx])))
    rw [List.length_erase_of_mem present] at smaller
    have positive : 0 < supply.length := by
      cases supply with
      | nil => simp at present
      | cons a l => simp
    simp only [List.length_cons]
    omega

/-- Any pairwise conflicting family consumes one separate word per member. -/
theorem cliqueCapacity {I W : Type} [DecidableEq W] (family : List I)
    (conflict : I → I → Prop) (word : I → W) (supply : List W)
    (clique : family.Pairwise conflict)
    (apart : ∀ i j, conflict i j → word i ≠ word j)
    (inside : ∀ i ∈ family, word i ∈ supply) : family.length ≤ supply.length := by
  have nd : (family.map word).Nodup := List.pairwise_map.mpr (clique.imp (fun h => apart _ _ h))
  have cap := capacity nd supply (by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact inside i hi)
  simpa using cap

def chosen : List Nat :=
  [0,2,4,6,10,12,14,16,18,20,22,24,28,30,32,34,36,42,44,46,48,50,56,58,
   60,68,70,72,74,76,80,82,84]

def hamming (x y : Nat) : Nat :=
  ((List.range 9).filter fun bit => (x.testBit bit) != (y.testBit bit)).length

def supply (p : Bool) : List Nat :=
  (List.range 64).filter fun w => decide ((hamming w 0) % 2 = 1) == p

theorem supply_size (p : Bool) : (supply p).length = 32 := by cases p <;> decide

theorem impossible (p : Bool) (word : Nat → Nat) (conflict : Nat → Nat → Prop)
    (clique : chosen.Pairwise conflict)
    (apart : ∀ i j, conflict i j → word i ≠ word j)
    (inside : ∀ i ∈ chosen, word i ∈ supply p) : False := by
  have h := cliqueCapacity chosen conflict word (supply p) clique apart inside
  rw [supply_size] at h
  have length : chosen.length = 33 := by decide
  omega

#print axioms capacity
#print axioms cliqueCapacity
#print axioms impossible

def source : List Nat :=
  [0,1,17,19,18,22,6,70,326,327,335,333,349,348,350,346,338,339,337,321,320,328,72,200,
   192,193,209,211,210,214,222,220,221,205,207,199,135,151,149,148,132,140,142,138,154,155,
   153,137,393,397,413,412,414,406,390,422,486,487,495,493,509,508,510,506,498,499,497,481,
   480,488,424,296,288,289,305,307,306,310,318,316,317,301,303,295,39,55,53,52,36,44,46,42,
   58,59,57,41,105,109,125,124,126,118,114,112,368,376,377,379,383,375,373,357,356,364,366,
   362,354,355,99,227,226,234,238,236,228,244,245,247,255,251,249,248,184,188,190,182,178,
   179,177,161,165,173,175,171,427,443,447,439,437,436,432,400,464,472,473,475,479,471,469,
   453,452,460,462,458,450,451,387,259,258,266,270,268,260,261,277,279,287,283,281,280,24,
   28,29,13,15,11,75,91,95,87,85,84]

def candidate := source.take 191 ++ [source[190]! ^^^ 16, source[191]! ^^^ 16]
def base (i : Nat) := candidate[i]! &&& 19

/-- Index the first interval by zero. Its word changes exactly at a repeated base. -/
def run : Nat → Nat
  | 0 => 0
  | i+1 => run i + (if base i = base (i+1) then 1 else 0)

/-- Retain the actual path positions in each interval. -/
def positions (r : Nat) := (List.range 193).filter fun i => run i == r

def conflictB (r s : Nat) : Bool :=
  (positions r).any fun i => (positions s).any fun j =>
    decide (i+1<j ∧ hamming (base i) (base j) ≤ 1)

theorem conflict_sound {r s : Nat} (h : conflictB r s = true) :
    ∃ i j, i<193 ∧ j<193 ∧ run i=r ∧ run j=s ∧ i+1<j ∧ hamming (base i) (base j)≤1 := by
  simp only [conflictB, positions, List.any_eq_true, List.mem_filter, List.mem_range,
    beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨i, ⟨hi,hr⟩, j, ⟨hj,hs⟩, hij, hd⟩ := h
  exact ⟨i,j,hi,hj,hr,hs,hij,hd⟩

theorem apart_of_induced (word : Nat → Nat)
    (nonedge : ∀ i j, i<193 → j<193 → i+1<j →
      2 ≤ hamming (base i) (base j) + hamming (word (run i)) (word (run j))) :
    ∀ r s, conflictB r s = true → word r ≠ word s := by
  intro r s h same
  obtain ⟨i,j,hi,hj,hr,hs,hij,hd⟩ := conflict_sound h
  have hsep := nonedge i j hi hj hij
  have self (x : Nat) : hamming x x = 0 := by simp [hamming]
  rw [hr,hs,same,self] at hsep
  omega

#print axioms apart_of_induced
end Entry87
