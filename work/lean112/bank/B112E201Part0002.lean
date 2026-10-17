import B112E201Part0001
namespace B112E201
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c800 : List Lit := [(403, false)]
theorem step800 (p : Nat → Bool) (h : Constraints p) : clause p c800 = true :=
  Snake9.LocalRup.prove_clause [c778, c394] c800 (by decide) p (sat_cons (step778 p h) (sat_cons (step394 p h) (sat_nil p)))
def c801 : List Lit := [(395, false)]
theorem step801 (p : Nat → Bool) (h : Constraints p) : clause p c801 = true :=
  Snake9.LocalRup.prove_clause [c779, c382] c801 (by decide) p (sat_cons (step779 p h) (sat_cons (step382 p h) (sat_nil p)))
def c802 : List Lit := [(389, false)]
theorem step802 (p : Nat → Bool) (h : Constraints p) : clause p c802 = true :=
  Snake9.LocalRup.prove_clause [c779, c383] c802 (by decide) p (sat_cons (step779 p h) (sat_cons (step383 p h) (sat_nil p)))
def c803 : List Lit := [(383, false)]
theorem step803 (p : Nat → Bool) (h : Constraints p) : clause p c803 = true :=
  Snake9.LocalRup.prove_clause [c780, c374] c803 (by decide) p (sat_cons (step780 p h) (sat_cons (step374 p h) (sat_nil p)))
def c804 : List Lit := [(379, false)]
theorem step804 (p : Nat → Bool) (h : Constraints p) : clause p c804 = true :=
  Snake9.LocalRup.prove_clause [c780, c375] c804 (by decide) p (sat_cons (step780 p h) (sat_cons (step375 p h) (sat_nil p)))
def c805 : List Lit := [(369, false)]
theorem step805 (p : Nat → Bool) (h : Constraints p) : clause p c805 = true :=
  Snake9.LocalRup.prove_clause [c781, c361] c805 (by decide) p (sat_cons (step781 p h) (sat_cons (step361 p h) (sat_nil p)))
def c806 : List Lit := [(363, false)]
theorem step806 (p : Nat → Bool) (h : Constraints p) : clause p c806 = true :=
  Snake9.LocalRup.prove_clause [c781, c362] c806 (by decide) p (sat_cons (step781 p h) (sat_cons (step362 p h) (sat_nil p)))
def c807 : List Lit := [(357, false)]
theorem step807 (p : Nat → Bool) (h : Constraints p) : clause p c807 = true :=
  Snake9.LocalRup.prove_clause [c782, c352] c807 (by decide) p (sat_cons (step782 p h) (sat_cons (step352 p h) (sat_nil p)))
def c808 : List Lit := [(351, false)]
theorem step808 (p : Nat → Bool) (h : Constraints p) : clause p c808 = true :=
  Snake9.LocalRup.prove_clause [c782, c354] c808 (by decide) p (sat_cons (step782 p h) (sat_cons (step354 p h) (sat_nil p)))
def c809 : List Lit := [(343, false)]
theorem step809 (p : Nat → Bool) (h : Constraints p) : clause p c809 = true :=
  Snake9.LocalRup.prove_clause [c783, c335] c809 (by decide) p (sat_cons (step783 p h) (sat_cons (step335 p h) (sat_nil p)))
def c810 : List Lit := [(337, false)]
theorem step810 (p : Nat → Bool) (h : Constraints p) : clause p c810 = true :=
  Snake9.LocalRup.prove_clause [c783, c336] c810 (by decide) p (sat_cons (step783 p h) (sat_cons (step336 p h) (sat_nil p)))
def c811 : List Lit := [(331, false)]
theorem step811 (p : Nat → Bool) (h : Constraints p) : clause p c811 = true :=
  Snake9.LocalRup.prove_clause [c784, c325] c811 (by decide) p (sat_cons (step784 p h) (sat_cons (step325 p h) (sat_nil p)))
def c812 : List Lit := [(327, false)]
theorem step812 (p : Nat → Bool) (h : Constraints p) : clause p c812 = true :=
  Snake9.LocalRup.prove_clause [c784, c326] c812 (by decide) p (sat_cons (step784 p h) (sat_cons (step326 p h) (sat_nil p)))
def c813 : List Lit := [(162, false)]
theorem step813 (p : Nat → Bool) (h : Constraints p) : clause p c813 = true :=
  Snake9.LocalRup.prove_clause [c785, c305] c813 (by decide) p (sat_cons (step785 p h) (sat_cons (step305 p h) (sat_nil p)))
def c814 : List Lit := [(160, false)]
theorem step814 (p : Nat → Bool) (h : Constraints p) : clause p c814 = true :=
  Snake9.LocalRup.prove_clause [c786, c304] c814 (by decide) p (sat_cons (step786 p h) (sat_cons (step304 p h) (sat_nil p)))
def c815 : List Lit := [(158, false)]
theorem step815 (p : Nat → Bool) (h : Constraints p) : clause p c815 = true :=
  Snake9.LocalRup.prove_clause [c787, c302] c815 (by decide) p (sat_cons (step787 p h) (sat_cons (step302 p h) (sat_nil p)))
def c816 : List Lit := [(155, false)]
theorem step816 (p : Nat → Bool) (h : Constraints p) : clause p c816 = true :=
  Snake9.LocalRup.prove_clause [c788, c297] c816 (by decide) p (sat_cons (step788 p h) (sat_cons (step297 p h) (sat_nil p)))
def c817 : List Lit := [(154, false)]
theorem step817 (p : Nat → Bool) (h : Constraints p) : clause p c817 = true :=
  Snake9.LocalRup.prove_clause [c789, c296] c817 (by decide) p (sat_cons (step789 p h) (sat_cons (step296 p h) (sat_nil p)))
def c818 : List Lit := [(152, false)]
theorem step818 (p : Nat → Bool) (h : Constraints p) : clause p c818 = true :=
  Snake9.LocalRup.prove_clause [c790, c294] c818 (by decide) p (sat_cons (step790 p h) (sat_cons (step294 p h) (sat_nil p)))
def c819 : List Lit := [(149, false)]
theorem step819 (p : Nat → Bool) (h : Constraints p) : clause p c819 = true :=
  Snake9.LocalRup.prove_clause [c791, c285] c819 (by decide) p (sat_cons (step791 p h) (sat_cons (step285 p h) (sat_nil p)))
def c820 : List Lit := [(147, false)]
theorem step820 (p : Nat → Bool) (h : Constraints p) : clause p c820 = true :=
  Snake9.LocalRup.prove_clause [c792, c284] c820 (by decide) p (sat_cons (step792 p h) (sat_cons (step284 p h) (sat_nil p)))
def c821 : List Lit := [(144, false)]
theorem step821 (p : Nat → Bool) (h : Constraints p) : clause p c821 = true :=
  Snake9.LocalRup.prove_clause [c793, c281] c821 (by decide) p (sat_cons (step793 p h) (sat_cons (step281 p h) (sat_nil p)))
def c822 : List Lit := [(417, false)]
theorem step822 (p : Nat → Bool) (h : Constraints p) : clause p c822 = true :=
  Snake9.LocalRup.prove_clause [c797, c400] c822 (by decide) p (sat_cons (step797 p h) (sat_cons (step400 p h) (sat_nil p)))
def c823 : List Lit := [(413, false)]
theorem step823 (p : Nat → Bool) (h : Constraints p) : clause p c823 = true :=
  Snake9.LocalRup.prove_clause [c798, c396] c823 (by decide) p (sat_cons (step798 p h) (sat_cons (step396 p h) (sat_nil p)))
def c824 : List Lit := [(212, false)]
theorem step824 (p : Nat → Bool) (h : Constraints p) : clause p c824 = true :=
  Snake9.LocalRup.prove_clause [c798, c397] c824 (by decide) p (sat_cons (step798 p h) (sat_cons (step397 p h) (sat_nil p)))
def c825 : List Lit := [(405, false)]
theorem step825 (p : Nat → Bool) (h : Constraints p) : clause p c825 = true :=
  Snake9.LocalRup.prove_clause [c799, c392] c825 (by decide) p (sat_cons (step799 p h) (sat_cons (step392 p h) (sat_nil p)))
def c826 : List Lit := [(401, false)]
theorem step826 (p : Nat → Bool) (h : Constraints p) : clause p c826 = true :=
  Snake9.LocalRup.prove_clause [c800, c389] c826 (by decide) p (sat_cons (step800 p h) (sat_cons (step389 p h) (sat_nil p)))
def c827 : List Lit := [(205, false)]
theorem step827 (p : Nat → Bool) (h : Constraints p) : clause p c827 = true :=
  Snake9.LocalRup.prove_clause [c800, c390] c827 (by decide) p (sat_cons (step800 p h) (sat_cons (step390 p h) (sat_nil p)))
def c828 : List Lit := [(393, false)]
theorem step828 (p : Nat → Bool) (h : Constraints p) : clause p c828 = true :=
  Snake9.LocalRup.prove_clause [c801, c380] c828 (by decide) p (sat_cons (step801 p h) (sat_cons (step380 p h) (sat_nil p)))
def c829 : List Lit := [(391, false)]
theorem step829 (p : Nat → Bool) (h : Constraints p) : clause p c829 = true :=
  Snake9.LocalRup.prove_clause [c801, c381] c829 (by decide) p (sat_cons (step801 p h) (sat_cons (step381 p h) (sat_nil p)))
def c830 : List Lit := [(197, false)]
theorem step830 (p : Nat → Bool) (h : Constraints p) : clause p c830 = true :=
  Snake9.LocalRup.prove_clause [c802, c377] c830 (by decide) p (sat_cons (step802 p h) (sat_cons (step377 p h) (sat_nil p)))
def c831 : List Lit := [(381, false)]
theorem step831 (p : Nat → Bool) (h : Constraints p) : clause p c831 = true :=
  Snake9.LocalRup.prove_clause [c803, c372] c831 (by decide) p (sat_cons (step803 p h) (sat_cons (step372 p h) (sat_nil p)))
def c832 : List Lit := [(194, false)]
theorem step832 (p : Nat → Bool) (h : Constraints p) : clause p c832 = true :=
  Snake9.LocalRup.prove_clause [c803, c373] c832 (by decide) p (sat_cons (step803 p h) (sat_cons (step373 p h) (sat_nil p)))
def c833 : List Lit := [(191, false)]
theorem step833 (p : Nat → Bool) (h : Constraints p) : clause p c833 = true :=
  Snake9.LocalRup.prove_clause [c804, c370] c833 (by decide) p (sat_cons (step804 p h) (sat_cons (step370 p h) (sat_nil p)))
def c834 : List Lit := [(367, false)]
theorem step834 (p : Nat → Bool) (h : Constraints p) : clause p c834 = true :=
  Snake9.LocalRup.prove_clause [c805, c359] c834 (by decide) p (sat_cons (step805 p h) (sat_cons (step359 p h) (sat_nil p)))
def c835 : List Lit := [(365, false)]
theorem step835 (p : Nat → Bool) (h : Constraints p) : clause p c835 = true :=
  Snake9.LocalRup.prove_clause [c805, c360] c835 (by decide) p (sat_cons (step805 p h) (sat_cons (step360 p h) (sat_nil p)))
def c836 : List Lit := [(361, false)]
theorem step836 (p : Nat → Bool) (h : Constraints p) : clause p c836 = true :=
  Snake9.LocalRup.prove_clause [c806, c356] c836 (by decide) p (sat_cons (step806 p h) (sat_cons (step356 p h) (sat_nil p)))
def c837 : List Lit := [(355, false)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.LocalRup.prove_clause [c807, c349] c837 (by decide) p (sat_cons (step807 p h) (sat_cons (step349 p h) (sat_nil p)))
def c838 : List Lit := [(353, false)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c807, c350] c838 (by decide) p (sat_cons (step807 p h) (sat_cons (step350 p h) (sat_nil p)))
def c839 : List Lit := [(349, false)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c808, c344] c839 (by decide) p (sat_cons (step808 p h) (sat_cons (step344 p h) (sat_nil p)))
def c840 : List Lit := [(341, false)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c809, c333] c840 (by decide) p (sat_cons (step809 p h) (sat_cons (step333 p h) (sat_nil p)))
def c841 : List Lit := [(339, false)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c809, c334] c841 (by decide) p (sat_cons (step809 p h) (sat_cons (step334 p h) (sat_nil p)))
def c842 : List Lit := [(335, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c810, c328] c842 (by decide) p (sat_cons (step810 p h) (sat_cons (step328 p h) (sat_nil p)))
def c843 : List Lit := [(170, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c810, c329] c843 (by decide) p (sat_cons (step810 p h) (sat_cons (step329 p h) (sat_nil p)))
def c844 : List Lit := [(329, false)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c811, c324] c844 (by decide) p (sat_cons (step811 p h) (sat_cons (step324 p h) (sat_nil p)))
def c845 : List Lit := [(325, false)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c812, c322] c845 (by decide) p (sat_cons (step812 p h) (sat_cons (step322 p h) (sat_nil p)))
def c846 : List Lit := [(46, false)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c816, c100] c846 (by decide) p (sat_cons (step816 p h) (sat_cons (step100 p h) (sat_nil p)))
def c847 : List Lit := [(216, false)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c822, c398] c847 (by decide) p (sat_cons (step822 p h) (sat_cons (step398 p h) (sat_nil p)))
def c848 : List Lit := [(215, false)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c822, c399] c848 (by decide) p (sat_cons (step822 p h) (sat_cons (step399 p h) (sat_nil p)))
def c849 : List Lit := [(214, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c823, c395] c849 (by decide) p (sat_cons (step823 p h) (sat_cons (step395 p h) (sat_nil p)))
def c850 : List Lit := [(209, false)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c825, c391] c850 (by decide) p (sat_cons (step825 p h) (sat_cons (step391 p h) (sat_nil p)))
def c851 : List Lit := [(207, false)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c826, c387] c851 (by decide) p (sat_cons (step826 p h) (sat_cons (step387 p h) (sat_nil p)))
def c852 : List Lit := [(206, false)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c826, c388] c852 (by decide) p (sat_cons (step826 p h) (sat_cons (step388 p h) (sat_nil p)))
def c853 : List Lit := [(203, false)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c828, c379] c853 (by decide) p (sat_cons (step828 p h) (sat_cons (step379 p h) (sat_nil p)))
def c854 : List Lit := [(200, false)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c829, c378] c854 (by decide) p (sat_cons (step829 p h) (sat_cons (step378 p h) (sat_nil p)))
def c855 : List Lit := [(196, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c831, c371] c855 (by decide) p (sat_cons (step831 p h) (sat_cons (step371 p h) (sat_nil p)))
def c856 : List Lit := [(189, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c834, c358] c856 (by decide) p (sat_cons (step834 p h) (sat_cons (step358 p h) (sat_nil p)))
def c857 : List Lit := [(188, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c835, c357] c857 (by decide) p (sat_cons (step835 p h) (sat_cons (step357 p h) (sat_nil p)))
def c858 : List Lit := [(186, false)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c836, c355] c858 (by decide) p (sat_cons (step836 p h) (sat_cons (step355 p h) (sat_nil p)))
def c859 : List Lit := [(183, false)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c837, c348] c859 (by decide) p (sat_cons (step837 p h) (sat_cons (step348 p h) (sat_nil p)))
def c860 : List Lit := [(181, false)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c838, c345] c860 (by decide) p (sat_cons (step838 p h) (sat_cons (step345 p h) (sat_nil p)))
def c861 : List Lit := [(180, false)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c838, c346] c861 (by decide) p (sat_cons (step838 p h) (sat_cons (step346 p h) (sat_nil p)))
def c862 : List Lit := [(178, false)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c839, c343] c862 (by decide) p (sat_cons (step839 p h) (sat_cons (step343 p h) (sat_nil p)))
def c863 : List Lit := [(175, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c840, c332] c863 (by decide) p (sat_cons (step840 p h) (sat_cons (step332 p h) (sat_nil p)))
end B112E201
