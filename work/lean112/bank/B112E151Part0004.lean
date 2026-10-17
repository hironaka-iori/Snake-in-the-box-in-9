import B112E151Part0003
namespace B112E151
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c837 : List Lit := [(835, true)]
theorem step837 (p : Nat → Bool) (h : Constraints p) : clause p c837 = true :=
  Snake9.TreeRup.prove_clause [c616, c825, c823, c617, c796, c196, c192, c197, c829, c820, c620, c831, c779, c188, c778, c408, c411, c404, c599, c374, c375, c353, c350, c364, c365, c342, c343, c362, c363, c41, c340, c337, c338, c40, c27, c632, c367, c330, c372, c336, c368, c43, c42, c833, c834, c556, c538, c535, c835, c482, c483, c161, c423, c425, c836, c471, c474, c497, c490, c629, c453, c467, c431, c420, c639, c8, c29, c31, c481, c740] c837 (by decide) p (sat_cons (step616 p h) (sat_cons (step825 p h) (sat_cons (step823 p h) (sat_cons (step617 p h) (sat_cons (step796 p h) (sat_cons (step196 p h) (sat_cons (step192 p h) (sat_cons (step197 p h) (sat_cons (step829 p h) (sat_cons (step820 p h) (sat_cons (step620 p h) (sat_cons (step831 p h) (sat_cons (step779 p h) (sat_cons (step188 p h) (sat_cons (step778 p h) (sat_cons (step408 p h) (sat_cons (step411 p h) (sat_cons (step404 p h) (sat_cons (step599 p h) (sat_cons (step374 p h) (sat_cons (step375 p h) (sat_cons (step353 p h) (sat_cons (step350 p h) (sat_cons (step364 p h) (sat_cons (step365 p h) (sat_cons (step342 p h) (sat_cons (step343 p h) (sat_cons (step362 p h) (sat_cons (step363 p h) (sat_cons (step41 p h) (sat_cons (step340 p h) (sat_cons (step337 p h) (sat_cons (step338 p h) (sat_cons (step40 p h) (sat_cons (step27 p h) (sat_cons (step632 p h) (sat_cons (step367 p h) (sat_cons (step330 p h) (sat_cons (step372 p h) (sat_cons (step336 p h) (sat_cons (step368 p h) (sat_cons (step43 p h) (sat_cons (step42 p h) (sat_cons (step833 p h) (sat_cons (step834 p h) (sat_cons (step556 p h) (sat_cons (step538 p h) (sat_cons (step535 p h) (sat_cons (step835 p h) (sat_cons (step482 p h) (sat_cons (step483 p h) (sat_cons (step161 p h) (sat_cons (step423 p h) (sat_cons (step425 p h) (sat_cons (step836 p h) (sat_cons (step471 p h) (sat_cons (step474 p h) (sat_cons (step497 p h) (sat_cons (step490 p h) (sat_cons (step629 p h) (sat_cons (step453 p h) (sat_cons (step467 p h) (sat_cons (step431 p h) (sat_cons (step420 p h) (sat_cons (step639 p h) (sat_cons (step8 p h) (sat_cons (step29 p h) (sat_cons (step31 p h) (sat_cons (step481 p h) (sat_cons (step740 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c838 : List Lit := [(954, false)]
theorem step838 (p : Nat → Bool) (h : Constraints p) : clause p c838 = true :=
  Snake9.LocalRup.prove_clause [c837, c569, c566] c838 (by decide) p (sat_cons (step837 p h) (sat_cons (step569 p h) (sat_cons (step566 p h) (sat_nil p))))
def c839 : List Lit := [(882, false)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c838, c821, c555] c839 (by decide) p (sat_cons (step838 p h) (sat_cons (step821 p h) (sat_cons (step555 p h) (sat_nil p))))
def c840 : List Lit := [(855, false)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c839, c621, c466] c840 (by decide) p (sat_cons (step839 p h) (sat_cons (step621 p h) (sat_cons (step466 p h) (sat_nil p))))
def c841 : List Lit := [(13, false)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c839, c834] c841 (by decide) p (sat_cons (step839 p h) (sat_cons (step834 p h) (sat_nil p)))
def c842 : List Lit := [(847, false)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c840, c433] c842 (by decide) p (sat_cons (step840 p h) (sat_cons (step433 p h) (sat_nil p)))
def c843 : List Lit := [(21, false), (22, false)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c782, c778, c779, c187, c841, c780, c582, c590, c7, c28, c5, c19, c2, c232, c225, c234, c226, c235, c229, c239] c843 (by decide) p (sat_cons (step782 p h) (sat_cons (step778 p h) (sat_cons (step779 p h) (sat_cons (step187 p h) (sat_cons (step841 p h) (sat_cons (step780 p h) (sat_cons (step582 p h) (sat_cons (step590 p h) (sat_cons (step7 p h) (sat_cons (step28 p h) (sat_cons (step5 p h) (sat_cons (step19 p h) (sat_cons (step2 p h) (sat_cons (step232 p h) (sat_cons (step225 p h) (sat_cons (step234 p h) (sat_cons (step226 p h) (sat_cons (step235 p h) (sat_cons (step229 p h) (sat_cons (step239 p h) (sat_nil p)))))))))))))))))))))
def c844 : List Lit := [(56, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c842, c840, c839, c620, c420, c421, c430, c431, c418, c464, c425, c630, c453, c441, c448] c844 (by decide) p (sat_cons (step842 p h) (sat_cons (step840 p h) (sat_cons (step839 p h) (sat_cons (step620 p h) (sat_cons (step420 p h) (sat_cons (step421 p h) (sat_cons (step430 p h) (sat_cons (step431 p h) (sat_cons (step418 p h) (sat_cons (step464 p h) (sat_cons (step425 p h) (sat_cons (step630 p h) (sat_cons (step453 p h) (sat_cons (step441 p h) (sat_cons (step448 p h) (sat_nil p))))))))))))))))
def c845 : List Lit := [(4, false)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c844, c779, c639] c845 (by decide) p (sat_cons (step844 p h) (sat_cons (step779 p h) (sat_cons (step639 p h) (sat_nil p))))
def c846 : List Lit := [(2, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c845, c187, c779, c5] c846 (by decide) p (sat_cons (step845 p h) (sat_cons (step187 p h) (sat_cons (step779 p h) (sat_cons (step5 p h) (sat_nil p)))))
def c847 : List Lit := [(21, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c845, c188, c778, c8] c847 (by decide) p (sat_cons (step845 p h) (sat_cons (step188 p h) (sat_cons (step778 p h) (sat_cons (step8 p h) (sat_nil p)))))
def c848 : List Lit := [(109, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c846, c582, c2] c848 (by decide) p (sat_cons (step846 p h) (sat_cons (step582 p h) (sat_cons (step2 p h) (sat_nil p))))
def c849 : List Lit := [(22, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c847, c843] c849 (by decide) p (sat_cons (step847 p h) (sat_cons (step843 p h) (sat_nil p)))
def c850 : List Lit := [(215, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c848, c225] c850 (by decide) p (sat_cons (step848 p h) (sat_cons (step225 p h) (sat_nil p)))
def c851 : List Lit := [(217, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c850, c226] c851 (by decide) p (sat_cons (step850 p h) (sat_cons (step226 p h) (sat_nil p)))
def c852 : List Lit := [(223, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c851, c229] c852 (by decide) p (sat_cons (step851 p h) (sat_cons (step229 p h) (sat_nil p)))
def c853 : List Lit := [(237, true)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c852, c238] c853 (by decide) p (sat_cons (step852 p h) (sat_cons (step238 p h) (sat_nil p)))
def c854 : List Lit := [(235, false)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c852, c590, c239] c854 (by decide) p (sat_cons (step852 p h) (sat_cons (step590 p h) (sat_cons (step239 p h) (sat_nil p))))
def c855 : List Lit := [(261, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c853, c588, c254] c855 (by decide) p (sat_cons (step853 p h) (sat_cons (step588 p h) (sat_cons (step254 p h) (sat_nil p))))
def c856 : List Lit := [(233, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c854, c235] c856 (by decide) p (sat_cons (step854 p h) (sat_cons (step235 p h) (sat_nil p)))
def c857 : List Lit := [(247, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c855, c251] c857 (by decide) p (sat_cons (step855 p h) (sat_cons (step251 p h) (sat_nil p)))
def c858 : List Lit := [(229, false)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c856, c234] c858 (by decide) p (sat_cons (step856 p h) (sat_cons (step234 p h) (sat_nil p)))
def c859 : List Lit := [(245, false)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c857, c244] c859 (by decide) p (sat_cons (step857 p h) (sat_cons (step244 p h) (sat_nil p)))
def c860 : List Lit := [(119, false)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c858, c232] c860 (by decide) p (sat_cons (step858 p h) (sat_cons (step232 p h) (sat_nil p)))
def c861 : List Lit := [(243, false)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c859, c242] c861 (by decide) p (sat_cons (step859 p h) (sat_cons (step242 p h) (sat_nil p)))
def c862 : List Lit := [(17, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c860, c780, c841, c19] c862 (by decide) p (sat_cons (step860 p h) (sat_cons (step780 p h) (sat_cons (step841 p h) (sat_cons (step19 p h) (sat_nil p)))))
def c863 : List Lit := [(126, false)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c861, c241] c863 (by decide) p (sat_cons (step861 p h) (sat_cons (step241 p h) (sat_nil p)))
def c864 : List Lit := [(18, false)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c862, c847, c780, c22] c864 (by decide) p (sat_cons (step862 p h) (sat_cons (step847 p h) (sat_cons (step780 p h) (sat_cons (step22 p h) (sat_nil p)))))
def c865 : List Lit := [(20, false)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c864, c192, c27] c865 (by decide) p (sat_cons (step864 p h) (sat_cons (step192 p h) (sat_cons (step27 p h) (sat_nil p))))
def c866 : List Lit := [(749, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c865, c849, c339] c866 (by decide) p (sat_cons (step865 p h) (sat_cons (step849 p h) (sat_cons (step339 p h) (sat_nil p))))
def c867 : List Lit := [(19, false)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c865, c863, c26] c867 (by decide) p (sat_cons (step865 p h) (sat_cons (step863 p h) (sat_cons (step26 p h) (sat_nil p))))
def c868 : List Lit := [(753, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c866, c345] c868 (by decide) p (sat_cons (step866 p h) (sat_cons (step345 p h) (sat_nil p)))
def c869 : List Lit := [(750, false)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c866, c832, c346] c869 (by decide) p (sat_cons (step866 p h) (sat_cons (step832 p h) (sat_cons (step346 p h) (sat_nil p))))
def c870 : List Lit := [(746, false)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c868, c830, c354] c870 (by decide) p (sat_cons (step868 p h) (sat_cons (step830 p h) (sat_cons (step354 p h) (sat_nil p))))
def c871 : List Lit := [(24, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c869, c341] c871 (by decide) p (sat_cons (step869 p h) (sat_cons (step341 p h) (sat_nil p)))
def c872 : List Lit := [(743, false)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c870, c841, c336] c872 (by decide) p (sat_cons (step870 p h) (sat_cons (step841 p h) (sat_cons (step336 p h) (sat_nil p))))
def c873 : List Lit := [(14, false)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c871, c867, c662] c873 (by decide) p (sat_cons (step871 p h) (sat_cons (step867 p h) (sat_cons (step662 p h) (sat_nil p))))
def c874 : List Lit := []
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c873, c872, c331] c874 (by decide) p (sat_cons (step873 p h) (sat_cons (step872 p h) (sat_cons (step331 p h) (sat_nil p))))
end B112E151
