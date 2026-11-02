import HistoryCountSupport
namespace Snake9.LocalWindow.CountPropagation65.CountPhase04
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def W : List Nat := [0, 1, 3, 7, 15, 31, 63, 55, 51, 50, 48, 56]
def dirs : List Nat := [0, 1, 2, 3, 4, 5, 3, 2, 0, 1, 3]
def D : List Nat := [17, 27, 33]
def c : Centre := ⟨51,2,0,0,2⟩
def bounds : List (Nat × Nat) := [(0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 21), (0, 2), (0, 21), (0, 21)]
theorem canonical : Canon W dirs := ⟨rfl,rfl,by decide +kernel⟩
theorem forced : forceCheckPlus W D=true := by decide +kernel
theorem three_corners : 3≤cnt (fun x => D.contains x) (corners c) := by decide +kernel
theorem local_lower (S : Nat → Bool) (hW : ∀ v∈W, S v=true)
    (hd : ∀ v, S v=true → cnt S (nbrs v)≤2) :
    3≤absentCorners S 51 2 0 := by
  have ha := forced_absent_plus S W D hW hd forced
  have hm := known_absent_count S D (corners c) ha
  rw [corners_count] at hm
  exact three_corners.trans hm
theorem in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+11≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0) :
    3≤coreAlpha p (r+8) := by
  by_contra hn
  have hs : coreAlpha p (r+8)≤2 := by omega
  have hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2 := by
    intro i hi
    have hi' : i<10 := by simpa [bounds] using hi
    by_cases hj : i=7
    · subst i
      simpa [bounds,Nat.add_assoc] using And.intro (Nat.zero_le (coreAlpha p (r+8))) hs
    · have he : bounds.getD i (0,21)=(0,21) := by
        interval_cases i <;> simp_all [bounds]
      rw [he]
      exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩
  have ax := frame_axioms p P r canonical (by decide) (by simpa [dirs] using hr) hP hb
  have hc : c∈centresOf W bounds := by
    rw [centresOf_canon canonical (by decide)]
    decide +kernel
  have ha := (ax.alpha c hc).2
  have hl := local_lower _ ax.window_sel ax.deg_le_two
  change absentCorners _ 51 2 0≤2 at ha
  omega
#print axioms canonical
#print axioms forced
#print axioms three_corners
#print axioms local_lower
#print axioms in_snake
end Snake9.LocalWindow.CountPropagation65.CountPhase04
