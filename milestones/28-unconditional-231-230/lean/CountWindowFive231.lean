import CountWindowFive231.P11
import CountWindowFive231.P12
import CountWindowFive231.P13
import CountWindowFive231.P14
import CountWindowFive231.P15
import CountWindowFive231.P16
import CountWindowFive231.P17
import CountWindowFive231.P18
import CountWindowFive231.P21
import CountWindowFive231.P22
import CountWindowFive231.P23
import CountWindowFive231.P24
import CountWindowFive231.P25
import CountWindowFive231.P26
import CountWindowFive231.P27
import CountWindowFive231.P28
import CountWindowFive231.P31
import CountWindowFive231.P32
import CountWindowFive231.P33
import CountWindowFive231.P34
import CountWindowFive231.P35
import CountWindowFive231.P36
import CountWindowFive231.P37
import CountWindowFive231.P38
import CountWindowFive231.P41
import CountWindowFive231.P42
import CountWindowFive231.P43
import CountWindowFive231.P44
import CountWindowFive231.P45
import CountWindowFive231.P46
import CountWindowFive231.P47
import CountWindowFive231.P48
import CountWindowFive231.P51
import CountWindowFive231.P52
import CountWindowFive231.P53
import CountWindowFive231.P54
import CountWindowFive231.P55
import CountWindowFive231.P56
import CountWindowFive231.P57
import CountWindowFive231.P58
import CountWindowFive231.P61
import CountWindowFive231.P62
import CountWindowFive231.P63
import CountWindowFive231.P64
import CountWindowFive231.P65
import CountWindowFive231.P66
import CountWindowFive231.P67
import CountWindowFive231.P68
import CountWindowFive231.P71
import CountWindowFive231.P72
import CountWindowFive231.P73
import CountWindowFive231.P74
import CountWindowFive231.P75
import CountWindowFive231.P76
import CountWindowFive231.P77
import CountWindowFive231.P78
import CountWindowFive231.P81
import CountWindowFive231.P82
import CountWindowFive231.P83
import CountWindowFive231.P84
import CountWindowFive231.P85
import CountWindowFive231.P86
import CountWindowFive231.P87
import CountWindowFive231.P88
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace Snake9.CountWindowFive231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
open CountWindowTable231 CountWindowTablePrefix231

theorem table_checked : prefixesCovered keys 6 = true := by
  simp only [prefixesCovered, allPositiveSyms, allBelow, Nat.reduceAdd,
    prefix11, prefix12, prefix13, prefix14, prefix15, prefix16, prefix17, prefix18, prefix21, prefix22, prefix23, prefix24, prefix25, prefix26, prefix27, prefix28, prefix31, prefix32, prefix33, prefix34, prefix35, prefix36, prefix37, prefix38, prefix41, prefix42, prefix43, prefix44, prefix45, prefix46, prefix47, prefix48, prefix51, prefix52, prefix53, prefix54, prefix55, prefix56, prefix57, prefix58, prefix61, prefix62, prefix63, prefix64, prefix65, prefix66, prefix67, prefix68, prefix71, prefix72, prefix73, prefix74, prefix75, prefix76, prefix77, prefix78, prefix81, prefix82, prefix83, prefix84, prefix85, prefix86, prefix87, prefix88, Bool.and_self]

theorem no_count_window (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m)
    (r : Nat) (hr : r + 6 ≤ m) :
    wforbK6R34C7W (dsOf p r 6) (symsK p 8 r 6) = false :=
  CountWindowTablePrefix231.no_window table_checked h p r (by decide) hr

/-- The original aggregate hw5 premise; concrete refutations remain explicit. -/
theorem hw5_of_counts (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m) :
    ∀ r, r + 6 ≤ m → wforbK6R34C7W
      [pathDir p r, pathDir p (r+1), pathDir p (r+2), pathDir p (r+3), pathDir p (r+4), pathDir p (r+5)]
      [symK 8 (countSeq p (r+1)), symK 8 (countSeq p (r+2)), symK 8 (countSeq p (r+3)), symK 8 (countSeq p (r+4)), symK 8 (countSeq p (r+5))] = false := by
  intro r hr
  rw [countSeq_eq_coreAlpha p (r+1) (by omega),
    countSeq_eq_coreAlpha p (r+2) (by omega),
    countSeq_eq_coreAlpha p (r+3) (by omega),
    countSeq_eq_coreAlpha p (r+4) (by omega),
    countSeq_eq_coreAlpha p (r+5) (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega),
    pathDir_eq_dir p (by omega)]
  exact no_count_window h p r hr

#print axioms table_checked
#print axioms no_count_window
#print axioms hw5_of_counts
end Snake9.CountWindowFive231
