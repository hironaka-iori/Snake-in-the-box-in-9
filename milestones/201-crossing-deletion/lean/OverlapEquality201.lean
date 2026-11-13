import AttachmentBalance191
namespace OverlapEquality201
open Replacement191
def bit (b : Bool) : Nat := if b then 1 else 0

theorem oneExact : ∀ p q r s : Bool,
    bit (p && q) + bit (p && q && !r && !s) +
      (bit (p && !q && !r)+bit (q && !p && !s)) =
    bit (p && q && r && s) + bit (p && !r)+bit (q && !s) := by
  decide +kernel

theorem exactOverlap {V : Type} (xs : List V) (p q r s : V → Bool) :
    count xs (fun v => p v && q v) +
      count xs (fun v => p v && q v && !r v && !s v) +
      (count xs (fun v => p v && !q v && !r v)+
       count xs (fun v => q v && !p v && !s v)) =
    count xs (fun v => p v && q v && r v && s v) +
      count xs (fun v => p v && !r v)+count xs (fun v => q v && !s v) := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    have h := oneExact (p v) (q v) (r v) (s v)
    simp only [count]
    unfold bit at h
    omega

theorem zeroCount {V : Type} (xs : List V) (f : V → Bool)
    (h : count xs f=0) : ∀ v ∈ xs, f v=false := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
    have hv : f v=false := by
      cases he : f v
      · rfl
      · simp [count,he] at h
    have ht : count vs f=0 := by simpa [count,hv] using h
    intro w hw
    rcases List.mem_cons.mp hw with eq | mem
    · simpa [eq] using hv
    · exact ih ht w mem

theorem saturatedOverlap {V : Type} (xs : List V) (p q r s : V → Bool)
    (tight : count xs (fun v => p v && q v) =
      count xs (fun v => p v && q v && r v && s v) +
      count xs (fun v => p v && !r v)+count xs (fun v => q v && !s v)) :
    ∀ v ∈ xs, (p v=true ∧ r v=false → q v=true ∧ s v=true) ∧
      (q v=true ∧ s v=false → p v=true ∧ r v=true) := by
  have he := exactOverlap xs p q r s
  have hz : count xs (fun v => p v && q v && !r v && !s v)=0 := by omega
  have hp : count xs (fun v => p v && !q v && !r v)=0 := by omega
  have hq : count xs (fun v => q v && !p v && !s v)=0 := by omega
  intro v hv
  have z := zeroCount xs _ hz v hv
  have a := zeroCount xs _ hp v hv
  have b := zeroCount xs _ hq v hv
  cases x : p v <;> cases y : q v <;> cases u : r v <;> cases w : s v <;> simp_all

#print axioms oneExact
#print axioms exactOverlap
#print axioms zeroCount
#print axioms saturatedOverlap
end OverlapEquality201
