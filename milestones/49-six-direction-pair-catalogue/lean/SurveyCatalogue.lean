import PairBasis4901
import PairBasis4902
import PairBasis4903
import PairBasis4904
import PairBasis4905
import PairBasis4906
import PairBasis4907
import PairBasis4908
import PairBasis4909
import PairBasis4910
import PairBasis4911
import PairBasis4912
import PairBasis4913
import PairBasis4914
import PairBasis4915
import PairBasis4916
import PairBasis4917
import PairBasis4918
import PairBasis4919
import PairBasis4920
import PairBasis4921
import PairBasis4922
import PairBasis4923
import PairBasis4924
import PairBasis4925
import PairBasis4926
import PairBasis4927
import PairBasis4928
import PairBasis4929
import PairBasis4930
import PairBasis4931
import PairBasis4932
import PairBasis4933
namespace Snake9.LocalWindow.SurveyCatalogue
set_option maxHeartbeats 0

theorem s0_p13_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,b] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4901.exclusion p (r+0) a b c
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s0_p13_c22

theorem s0_p14_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,b] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4902.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s0_p14_c22

theorem s0_p15_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,b] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4903.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s0_p15_c22

theorem s0_p15_c23 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,b] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4903.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s0_p15_c23

theorem s0_p15_c32 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,b] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4904.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s0_p15_c32

theorem s1_p13_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4901.exclusion p (r+0) a b c
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p13_c22

theorem s1_p13_c32 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4905.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p13_c32

theorem s1_p14_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4906.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p14_c22

theorem s1_p14_c23 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 3) : False := by
  apply PairBasis4906.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p14_c23

theorem s1_p24_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4907.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p24_c22

theorem s1_p24_c23 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 3) : False := by
  apply PairBasis4907.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p24_c23

theorem s1_p24_c32 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 3) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4907.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p24_c32

theorem s1_p24_c33 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 3) (hsecond : coreAlpha p (r+4) ≤ 3) : False := by
  apply PairBasis4907.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p24_c33

theorem s1_p25_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4908.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p25_c22

theorem s1_p25_c32 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 3) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4908.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p25_c32

theorem s1_p35_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+3) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4901.exclusion p (r+2) c a d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p35_c22

theorem s1_p35_c23 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,c] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+3) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4909.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s1_p35_c23

theorem s2_p13_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4901.exclusion p (r+0) a b c
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s2_p13_c22

theorem s2_p13_c32 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4910.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s2_p13_c32

theorem s2_p14_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4911.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s2_p14_c22

theorem s2_p15_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4912.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s2_p15_c22

theorem s2_p15_c23 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4912.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s2_p15_c23

theorem s2_p24_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,a,d,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4913.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s2_p24_c22

theorem s3_p15_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,b] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4914.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s3_p15_c22

theorem s4_p15_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4915.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s4_p15_c22

theorem s4_p15_c23 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4915.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s4_p15_c23

theorem s4_p15_c32 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4916.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s4_p15_c32

theorem s4_p45_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,a,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+4) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4917.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s4_p45_c22

theorem s5_p12_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+2) ≤ 2) : False := by
  apply PairBasis4918.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p12_c22

theorem s5_p13_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4919.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p13_c22

theorem s5_p13_c32 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+3) ≤ 2) : False := by
  apply PairBasis4919.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p13_c32

theorem s5_p14_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4920.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p14_c22

theorem s5_p24_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4901.exclusion p (r+1) b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p24_c22

theorem s5_p24_c23 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 3) : False := by
  apply PairBasis4921.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p24_c23

theorem s5_p24_c32 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 3) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4922.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p24_c32

theorem s5_p25_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4923.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p25_c22

theorem s5_p35_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+3) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4924.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p35_c22

theorem s5_p35_c23 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+3) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4924.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+3) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p35_c23

theorem s5_p45_c22 {m : Nat} (p : Snake m) (r a b c d : Nat)
    (hn : [a,b,c,d].Nodup) (h9 : ∀ x ∈ [a,b,c,d], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+4) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4925.exclusion p (r+0) a b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s5_p45_c22

theorem s6_p24_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,b,e] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+2) ≤ 2) (hsecond : coreAlpha p (r+4) ≤ 2) : False := by
  apply PairBasis4901.exclusion p (r+1) b c d
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s6_p24_c22

theorem s7_p12_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+2) ≤ 2) : False := by
  apply PairBasis4926.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s7_p12_c22

theorem s7_p15_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4927.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s7_p15_c22

theorem s7_p15_c23 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4927.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s7_p15_c23

theorem s7_p15_c32 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4928.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s7_p15_c32

theorem s7_p45_c22 {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,a] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+4) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4929.exclusion p (r+0) a b c d e
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s7_p45_c22

theorem s8_p12_c22 {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,f] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+2) ≤ 2) : False := by
  apply PairBasis4930.exclusion p (r+0) a b c d e f
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+2) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s8_p12_c22

theorem s8_p15_c22 {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,f] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4931.exclusion p (r+0) a b c d e f
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s8_p15_c22

theorem s8_p15_c23 {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,f] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 3) : False := by
  apply PairBasis4931.exclusion p (r+0) a b c d e f
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s8_p15_c23

theorem s8_p15_c32 {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,f] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+1) ≤ 3) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4932.exclusion p (r+0) a b c d e f
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+1) ≤ 3 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s8_p15_c32

theorem s8_p45_c22 {m : Nat} (p : Snake m) (r a b c d e f : Nat)
    (hn : [a,b,c,d,e,f].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e,f], x<9)
    (hr : r+6 ≤ m)
    (hd : ∀ j, j<6 → dir p (r+j) = ([a,b,c,d,e,f] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+4) ≤ 2) (hsecond : coreAlpha p (r+5) ≤ 2) : False := by
  apply PairBasis4933.exclusion p (r+0) a b c d e f
  · simp_all [List.nodup_cons] <;> omega
  · intro x hx
    apply h9 x
    simp only [List.mem_cons, List.mem_singleton] at hx ⊢
    tauto
  · omega
  · intro t ht
    interval_cases t
    · simpa [Nat.add_assoc] using hd 0 (by decide)
    · simpa [Nat.add_assoc] using hd 1 (by decide)
    · simpa [Nat.add_assoc] using hd 2 (by decide)
    · simpa [Nat.add_assoc] using hd 3 (by decide)
    · simpa [Nat.add_assoc] using hd 4 (by decide)
    · simpa [Nat.add_assoc] using hd 5 (by decide)
  · have hbound : coreAlpha p (r+4) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
  · have hbound : coreAlpha p (r+5) ≤ 2 := by omega
    simpa [Nat.add_assoc] using hbound
#print axioms s8_p45_c22
end Snake9.LocalWindow.SurveyCatalogue
