import B112E185Inputs
namespace B112E185
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c797 : List Lit := [(49, true)]
theorem step797 (p : Nat → Bool) (h : Constraints p) : clause p c797 = true :=
  Snake9.LocalRup.prove_clause [c154, c153] c797 (by decide) p (sat_cons (step154 p h) (sat_cons (step153 p h) (sat_nil p)))
def c798 : List Lit := [(157, true), (53, true)]
theorem step798 (p : Nat → Bool) (h : Constraints p) : clause p c798 = true :=
  Snake9.LocalRup.prove_clause [c797, c155] c798 (by decide) p (sat_cons (step797 p h) (sat_cons (step155 p h) (sat_nil p)))
def c799 : List Lit := [(53, false), (47, false), (52, false)]
theorem step799 (p : Nat → Bool) (h : Constraints p) : clause p c799 = true :=
  Snake9.LocalRup.prove_clause [c797, c161] c799 (by decide) p (sat_cons (step797 p h) (sat_cons (step161 p h) (sat_nil p)))
def c800 : List Lit := [(25, false)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true :=
  Snake9.LocalRup.prove_clause [c268, c94] c800 (by decide) p (sat_cons (step268 p h) (sat_cons (step94 p h) (sat_nil p)))
def c801 : List Lit := [(29, false)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true :=
  Snake9.LocalRup.prove_clause [c270, c101] c801 (by decide) p (sat_cons (step270 p h) (sat_cons (step101 p h) (sat_nil p)))
def c802 : List Lit := [(78, false)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true :=
  Snake9.LocalRup.prove_clause [c292, c209] c802 (by decide) p (sat_cons (step292 p h) (sat_cons (step209 p h) (sat_nil p)))
def c803 : List Lit := [(90, false)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true :=
  Snake9.LocalRup.prove_clause [c298, c233] c803 (by decide) p (sat_cons (step298 p h) (sat_cons (step233 p h) (sat_nil p)))
def c804 : List Lit := [(426, false)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true :=
  Snake9.LocalRup.prove_clause [c440, c437] c804 (by decide) p (sat_cons (step440 p h) (sat_cons (step437 p h) (sat_nil p)))
def c805 : List Lit := [(320, false)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true :=
  Snake9.LocalRup.prove_clause [c440, c439] c805 (by decide) p (sat_cons (step440 p h) (sat_cons (step439 p h) (sat_nil p)))
def c806 : List Lit := [(424, false)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true :=
  Snake9.LocalRup.prove_clause [c804, c433] c806 (by decide) p (sat_cons (step804 p h) (sat_cons (step433 p h) (sat_nil p)))
def c807 : List Lit := [(372, false)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true :=
  Snake9.LocalRup.prove_clause [c804, c436] c807 (by decide) p (sat_cons (step804 p h) (sat_cons (step436 p h) (sat_nil p)))
def c808 : List Lit := [(318, false)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true :=
  Snake9.LocalRup.prove_clause [c805, c368] c808 (by decide) p (sat_cons (step805 p h) (sat_cons (step368 p h) (sat_nil p)))
def c809 : List Lit := [(396, false)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true :=
  Snake9.LocalRup.prove_clause [c806, c431] c809 (by decide) p (sat_cons (step806 p h) (sat_cons (step431 p h) (sat_nil p)))
def c810 : List Lit := [(370, false)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true :=
  Snake9.LocalRup.prove_clause [c807, c400] c810 (by decide) p (sat_cons (step807 p h) (sat_cons (step400 p h) (sat_nil p)))
def c811 : List Lit := [(344, false)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true :=
  Snake9.LocalRup.prove_clause [c807, c403] c811 (by decide) p (sat_cons (step807 p h) (sat_cons (step403 p h) (sat_nil p)))
def c812 : List Lit := [(316, false)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true :=
  Snake9.LocalRup.prove_clause [c808, c363] c812 (by decide) p (sat_cons (step808 p h) (sat_cons (step363 p h) (sat_nil p)))
def c813 : List Lit := [(290, false)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true :=
  Snake9.LocalRup.prove_clause [c808, c366] c813 (by decide) p (sat_cons (step808 p h) (sat_cons (step366 p h) (sat_nil p)))
def c814 : List Lit := [(382, false)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true :=
  Snake9.LocalRup.prove_clause [c809, c418] c814 (by decide) p (sat_cons (step809 p h) (sat_cons (step418 p h) (sat_nil p)))
def c815 : List Lit := [(356, false)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true :=
  Snake9.LocalRup.prove_clause [c810, c398] c815 (by decide) p (sat_cons (step810 p h) (sat_cons (step398 p h) (sat_nil p)))
def c816 : List Lit := [(330, false)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true :=
  Snake9.LocalRup.prove_clause [c811, c385] c816 (by decide) p (sat_cons (step811 p h) (sat_cons (step385 p h) (sat_nil p)))
def c817 : List Lit := [(314, false)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c812, c358] c817 (by decide) p (sat_cons (step812 p h) (sat_cons (step358 p h) (sat_nil p)))
def c818 : List Lit := [(302, false)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c812, c361] c818 (by decide) p (sat_cons (step812 p h) (sat_cons (step361 p h) (sat_nil p)))
def c819 : List Lit := [(288, false)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c813, c333] c819 (by decide) p (sat_cons (step813 p h) (sat_cons (step333 p h) (sat_nil p)))
def c820 : List Lit := [(276, false)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c813, c335] c820 (by decide) p (sat_cons (step813 p h) (sat_cons (step335 p h) (sat_nil p)))
def c821 : List Lit := [(354, false)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c815, c392] c821 (by decide) p (sat_cons (step815 p h) (sat_cons (step392 p h) (sat_nil p)))
def c822 : List Lit := [(328, false)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true :=
  Snake9.LocalRup.prove_clause [c816, c376] c822 (by decide) p (sat_cons (step816 p h) (sat_cons (step376 p h) (sat_nil p)))
def c823 : List Lit := [(306, false)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c817, c356] c823 (by decide) p (sat_cons (step817 p h) (sat_cons (step356 p h) (sat_nil p)))
def c824 : List Lit := [(294, false)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c818, c346] c824 (by decide) p (sat_cons (step818 p h) (sat_cons (step346 p h) (sat_nil p)))
def c825 : List Lit := [(304, false)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c823, c351] c825 (by decide) p (sat_cons (step823 p h) (sat_cons (step351 p h) (sat_nil p)))
def c826 : List Lit := [(292, false)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c824, c340] c826 (by decide) p (sat_cons (step824 p h) (sat_cons (step340 p h) (sat_nil p)))
def c827 : List Lit := [(770, true)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c800, c488] c827 (by decide) p (sat_cons (step800 p h) (sat_cons (step488 p h) (sat_nil p)))
def c828 : List Lit := [(24, true), (771, true)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c800, c489] c828 (by decide) p (sat_cons (step800 p h) (sat_cons (step489 p h) (sat_nil p)))
def c829 : List Lit := [(772, true)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c827, c490] c829 (by decide) p (sat_cons (step827 p h) (sat_cons (step490 p h) (sat_nil p)))
def c830 : List Lit := [(768, false), (773, true)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c827, c491] c830 (by decide) p (sat_cons (step827 p h) (sat_cons (step491 p h) (sat_nil p)))
def c831 : List Lit := [(769, false), (774, true)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c827, c493] c831 (by decide) p (sat_cons (step827 p h) (sat_cons (step493 p h) (sat_nil p)))
def c832 : List Lit := [(776, true)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c829, c495] c832 (by decide) p (sat_cons (step829 p h) (sat_cons (step495 p h) (sat_nil p)))
def c833 : List Lit := [(765, false), (777, true)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c829, c498] c833 (by decide) p (sat_cons (step829 p h) (sat_cons (step498 p h) (sat_nil p)))
def c834 : List Lit := [(767, false), (779, true)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c829, c504] c834 (by decide) p (sat_cons (step829 p h) (sat_cons (step504 p h) (sat_nil p)))
def c835 : List Lit := [(758, false), (786, true)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c832, c510] c835 (by decide) p (sat_cons (step832 p h) (sat_cons (step510 p h) (sat_nil p)))
def c836 : List Lit := [(759, false), (787, true)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c832, c515] c836 (by decide) p (sat_cons (step832 p h) (sat_cons (step515 p h) (sat_nil p)))
def c837 : List Lit := [(760, false), (788, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c832, c519] c837 (by decide) p (sat_cons (step832 p h) (sat_cons (step519 p h) (sat_nil p)))
def c838 : List Lit := [(797, true)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c801, c522] c838 (by decide) p (sat_cons (step801 p h) (sat_cons (step522 p h) (sat_nil p)))
def c839 : List Lit := [(31, true), (798, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c801, c523] c839 (by decide) p (sat_cons (step801 p h) (sat_cons (step523 p h) (sat_nil p)))
def c840 : List Lit := [(799, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c838, c524] c840 (by decide) p (sat_cons (step838 p h) (sat_cons (step524 p h) (sat_nil p)))
def c841 : List Lit := [(27, true), (800, true)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c838, c526] c841 (by decide) p (sat_cons (step838 p h) (sat_cons (step526 p h) (sat_nil p)))
def c842 : List Lit := [(810, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c840, c542] c842 (by decide) p (sat_cons (step840 p h) (sat_cons (step542 p h) (sat_nil p)))
def c843 : List Lit := [(806, false), (811, true)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c840, c543] c843 (by decide) p (sat_cons (step840 p h) (sat_cons (step543 p h) (sat_nil p)))
def c844 : List Lit := [(807, false), (812, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c840, c544] c844 (by decide) p (sat_cons (step840 p h) (sat_cons (step544 p h) (sat_nil p)))
def c845 : List Lit := [(808, false), (813, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c840, c545] c845 (by decide) p (sat_cons (step840 p h) (sat_cons (step545 p h) (sat_nil p)))
def c846 : List Lit := [(809, false), (814, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c840, c546] c846 (by decide) p (sat_cons (step840 p h) (sat_cons (step546 p h) (sat_nil p)))
def c847 : List Lit := [(830, false), (838, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c842, c575] c847 (by decide) p (sat_cons (step842 p h) (sat_cons (step575 p h) (sat_nil p)))
def c848 : List Lit := [(832, false), (840, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c842, c576] c848 (by decide) p (sat_cons (step842 p h) (sat_cons (step576 p h) (sat_nil p)))
def c849 : List Lit := [(894, true)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c802, c644] c849 (by decide) p (sat_cons (step802 p h) (sat_cons (step644 p h) (sat_nil p)))
def c850 : List Lit := [(79, true), (895, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c802, c645] c850 (by decide) p (sat_cons (step802 p h) (sat_cons (step645 p h) (sat_nil p)))
def c851 : List Lit := [(896, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c849, c646] c851 (by decide) p (sat_cons (step849 p h) (sat_cons (step646 p h) (sat_nil p)))
def c852 : List Lit := [(892, false), (897, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c849, c648] c852 (by decide) p (sat_cons (step849 p h) (sat_cons (step648 p h) (sat_nil p)))
def c853 : List Lit := [(893, false), (898, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c849, c650] c853 (by decide) p (sat_cons (step849 p h) (sat_cons (step650 p h) (sat_nil p)))
def c854 : List Lit := [(900, true)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c851, c651] c854 (by decide) p (sat_cons (step851 p h) (sat_cons (step651 p h) (sat_nil p)))
def c855 : List Lit := [(889, false), (901, true)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c851, c654] c855 (by decide) p (sat_cons (step851 p h) (sat_cons (step654 p h) (sat_nil p)))
def c856 : List Lit := [(890, false), (902, true)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c851, c657] c856 (by decide) p (sat_cons (step851 p h) (sat_cons (step657 p h) (sat_nil p)))
def c857 : List Lit := [(891, false), (903, true)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c851, c659] c857 (by decide) p (sat_cons (step851 p h) (sat_cons (step659 p h) (sat_nil p)))
def c858 : List Lit := [(907, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c854, c660] c858 (by decide) p (sat_cons (step854 p h) (sat_cons (step660 p h) (sat_nil p)))
def c859 : List Lit := [(880, false), (908, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c854, c661] c859 (by decide) p (sat_cons (step854 p h) (sat_cons (step661 p h) (sat_nil p)))
def c860 : List Lit := [(881, false), (909, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c854, c664] c860 (by decide) p (sat_cons (step854 p h) (sat_cons (step664 p h) (sat_nil p)))
end B112E185
