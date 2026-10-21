import CountWindowFour231.P11
import CountWindowFour231.P12
import CountWindowFour231.P13
import CountWindowFour231.P14
import CountWindowFour231.P15
import CountWindowFour231.P16
import CountWindowFour231.P17
import CountWindowFour231.P18
import CountWindowFour231.P21
import CountWindowFour231.P22
import CountWindowFour231.P23
import CountWindowFour231.P24
import CountWindowFour231.P25
import CountWindowFour231.P26
import CountWindowFour231.P27
import CountWindowFour231.P28
import CountWindowFour231.P31
import CountWindowFour231.P32
import CountWindowFour231.P33
import CountWindowFour231.P34
import CountWindowFour231.P35
import CountWindowFour231.P36
import CountWindowFour231.P37
import CountWindowFour231.P38
import CountWindowFour231.P41
import CountWindowFour231.P42
import CountWindowFour231.P43
import CountWindowFour231.P44
import CountWindowFour231.P45
import CountWindowFour231.P46
import CountWindowFour231.P47
import CountWindowFour231.P48
import CountWindowFour231.P51
import CountWindowFour231.P52
import CountWindowFour231.P53
import CountWindowFour231.P54
import CountWindowFour231.P55
import CountWindowFour231.P56
import CountWindowFour231.P57
import CountWindowFour231.P58
import CountWindowFour231.P61
import CountWindowFour231.P62
import CountWindowFour231.P63
import CountWindowFour231.P64
import CountWindowFour231.P65
import CountWindowFour231.P66
import CountWindowFour231.P67
import CountWindowFour231.P68
import CountWindowFour231.P71
import CountWindowFour231.P72
import CountWindowFour231.P73
import CountWindowFour231.P74
import CountWindowFour231.P75
import CountWindowFour231.P76
import CountWindowFour231.P77
import CountWindowFour231.P78
import CountWindowFour231.P81
import CountWindowFour231.P82
import CountWindowFour231.P83
import CountWindowFour231.P84
import CountWindowFour231.P85
import CountWindowFour231.P86
import CountWindowFour231.P87
import CountWindowFour231.P88
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Snake9.CountWindowFour231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
open CountWindowTable231 CountWindowTablePrefix231

theorem table_checked : prefixesCovered keys 5 = true := by
  simp only [prefixesCovered, allPositiveSyms, allBelow, Nat.reduceAdd,
    prefix11, prefix12, prefix13, prefix14, prefix15, prefix16, prefix17, prefix18, prefix21, prefix22, prefix23, prefix24, prefix25, prefix26, prefix27, prefix28, prefix31, prefix32, prefix33, prefix34, prefix35, prefix36, prefix37, prefix38, prefix41, prefix42, prefix43, prefix44, prefix45, prefix46, prefix47, prefix48, prefix51, prefix52, prefix53, prefix54, prefix55, prefix56, prefix57, prefix58, prefix61, prefix62, prefix63, prefix64, prefix65, prefix66, prefix67, prefix68, prefix71, prefix72, prefix73, prefix74, prefix75, prefix76, prefix77, prefix78, prefix81, prefix82, prefix83, prefix84, prefix85, prefix86, prefix87, prefix88, Bool.and_self]

theorem no_count_window (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m)
    (r : Nat) (hr : r + 5 ≤ m) :
    wforbK6R34C7W (dsOf p r 5) (symsK p 8 r 5) = false :=
  CountWindowTablePrefix231.no_window table_checked h p r (by decide) hr

/-- The original aggregate hw4 premise; concrete refutations remain explicit. -/
theorem hw4_of_counts (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m) :
    ∀ r, r + 5 ≤ m → wforbK6R34C7W
      [pathDir p r, pathDir p (r+1), pathDir p (r+2), pathDir p (r+3), pathDir p (r+4)]
      [symK 8 (countSeq p (r+1)), symK 8 (countSeq p (r+2)), symK 8 (countSeq p (r+3)), symK 8 (countSeq p (r+4))] = false := by
  intro r hr
  rw [countSeq_eq_coreAlpha p (r+1) (by omega),
    countSeq_eq_coreAlpha p (r+2) (by omega),
    countSeq_eq_coreAlpha p (r+3) (by omega),
    countSeq_eq_coreAlpha p (r+4) (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega)]
  exact no_count_window h p r hr

#print axioms table_checked
#print axioms no_count_window
#print axioms hw4_of_counts
end Snake9.CountWindowFour231
