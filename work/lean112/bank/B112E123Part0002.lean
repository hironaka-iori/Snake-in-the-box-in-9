import B112E123Part0001
namespace B112E123
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c839 : List Lit := [(20, false), (23, true)]
theorem step839 (p : Nat → Bool) (h : Constraints p) : clause p c839 = true :=
  Snake9.LocalRup.prove_clause [c226, c103] c839 (by decide) p (sat_cons (step226 p h) (sat_cons (step103 p h) (sat_nil p)))
def c840 : List Lit := [(20, false), (3, true)]
theorem step840 (p : Nat → Bool) (h : Constraints p) : clause p c840 = true :=
  Snake9.LocalRup.prove_clause [c226, c104] c840 (by decide) p (sat_cons (step226 p h) (sat_cons (step104 p h) (sat_nil p)))
def c841 : List Lit := [(26, true), (23, true), (21, false)]
theorem step841 (p : Nat → Bool) (h : Constraints p) : clause p c841 = true :=
  Snake9.LocalRup.prove_clause [c227, c106] c841 (by decide) p (sat_cons (step227 p h) (sat_cons (step106 p h) (sat_nil p)))
def c842 : List Lit := [(26, true), (21, false), (22, true)]
theorem step842 (p : Nat → Bool) (h : Constraints p) : clause p c842 = true :=
  Snake9.LocalRup.prove_clause [c227, c107] c842 (by decide) p (sat_cons (step227 p h) (sat_cons (step107 p h) (sat_nil p)))
def c843 : List Lit := [(21, false), (23, true), (22, true)]
theorem step843 (p : Nat → Bool) (h : Constraints p) : clause p c843 = true :=
  Snake9.LocalRup.prove_clause [c227, c108] c843 (by decide) p (sat_cons (step227 p h) (sat_cons (step108 p h) (sat_nil p)))
def c844 : List Lit := [(21, true), (23, false), (133, true), (20, true)]
theorem step844 (p : Nat → Bool) (h : Constraints p) : clause p c844 = true :=
  Snake9.LocalRup.prove_clause [c711, c112] c844 (by decide) p (sat_cons (step711 p h) (sat_cons (step112 p h) (sat_nil p)))
def c845 : List Lit := [(21, true), (6, true), (23, false), (133, true)]
theorem step845 (p : Nat → Bool) (h : Constraints p) : clause p c845 = true :=
  Snake9.LocalRup.prove_clause [c711, c113] c845 (by decide) p (sat_cons (step711 p h) (sat_cons (step113 p h) (sat_nil p)))
def c846 : List Lit := [(24, false), (31, true)]
theorem step846 (p : Nat → Bool) (h : Constraints p) : clause p c846 = true :=
  Snake9.LocalRup.prove_clause [c228, c114] c846 (by decide) p (sat_cons (step228 p h) (sat_cons (step114 p h) (sat_nil p)))
def c847 : List Lit := [(24, false), (7, true)]
theorem step847 (p : Nat → Bool) (h : Constraints p) : clause p c847 = true :=
  Snake9.LocalRup.prove_clause [c228, c115] c847 (by decide) p (sat_cons (step228 p h) (sat_cons (step115 p h) (sat_nil p)))
def c848 : List Lit := [(27, false), (28, true), (22, true)]
theorem step848 (p : Nat → Bool) (h : Constraints p) : clause p c848 = true :=
  Snake9.LocalRup.prove_clause [c230, c118] c848 (by decide) p (sat_cons (step230 p h) (sat_cons (step118 p h) (sat_nil p)))
def c849 : List Lit := [(141, true), (32, true), (31, false)]
theorem step849 (p : Nat → Bool) (h : Constraints p) : clause p c849 = true :=
  Snake9.LocalRup.prove_clause [c712, c713, c124] c849 (by decide) p (sat_cons (step712 p h) (sat_cons (step713 p h) (sat_cons (step124 p h) (sat_nil p))))
def c850 : List Lit := [(31, false), (141, true), (24, true)]
theorem step850 (p : Nat → Bool) (h : Constraints p) : clause p c850 = true :=
  Snake9.LocalRup.prove_clause [c712, c713, c125] c850 (by decide) p (sat_cons (step712 p h) (sat_cons (step713 p h) (sat_cons (step125 p h) (sat_nil p))))
def c851 : List Lit := [(31, true), (32, false), (19, true)]
theorem step851 (p : Nat → Bool) (h : Constraints p) : clause p c851 = true :=
  Snake9.LocalRup.prove_clause [c233, c127] c851 (by decide) p (sat_cons (step233 p h) (sat_cons (step127 p h) (sat_nil p)))
def c852 : List Lit := [(28, true), (32, false), (19, true)]
theorem step852 (p : Nat → Bool) (h : Constraints p) : clause p c852 = true :=
  Snake9.LocalRup.prove_clause [c233, c128] c852 (by decide) p (sat_cons (step233 p h) (sat_cons (step128 p h) (sat_nil p)))
def c853 : List Lit := [(40, true), (35, true), (33, false)]
theorem step853 (p : Nat → Bool) (h : Constraints p) : clause p c853 = true :=
  Snake9.LocalRup.prove_clause [c234, c129] c853 (by decide) p (sat_cons (step234 p h) (sat_cons (step129 p h) (sat_nil p)))
def c854 : List Lit := [(34, true), (35, true), (33, false)]
theorem step854 (p : Nat → Bool) (h : Constraints p) : clause p c854 = true :=
  Snake9.LocalRup.prove_clause [c234, c130] c854 (by decide) p (sat_cons (step234 p h) (sat_cons (step130 p h) (sat_nil p)))
def c855 : List Lit := [(35, false), (42, false), (33, false)]
theorem step855 (p : Nat → Bool) (h : Constraints p) : clause p c855 = true :=
  Snake9.LocalRup.prove_clause [c149, c132] c855 (by decide) p (sat_cons (step149 p h) (sat_cons (step132 p h) (sat_nil p)))
def c856 : List Lit := [(40, true), (34, true), (41, false)]
theorem step856 (p : Nat → Bool) (h : Constraints p) : clause p c856 = true :=
  Snake9.LocalRup.prove_clause [c235, c144] c856 (by decide) p (sat_cons (step235 p h) (sat_cons (step144 p h) (sat_nil p)))
def c857 : List Lit := [(35, false), (53, false)]
theorem step857 (p : Nat → Bool) (h : Constraints p) : clause p c857 = true :=
  Snake9.LocalRup.prove_clause [c150, c148] c857 (by decide) p (sat_cons (step150 p h) (sat_cons (step148 p h) (sat_nil p)))
def c858 : List Lit := [(55, false), (53, true)]
theorem step858 (p : Nat → Bool) (h : Constraints p) : clause p c858 = true :=
  Snake9.LocalRup.prove_clause [c237, c151] c858 (by decide) p (sat_cons (step237 p h) (sat_cons (step151 p h) (sat_nil p)))
def c859 : List Lit := [(60, false), (59, true)]
theorem step859 (p : Nat → Bool) (h : Constraints p) : clause p c859 = true :=
  Snake9.LocalRup.prove_clause [c238, c154] c859 (by decide) p (sat_cons (step238 p h) (sat_cons (step154 p h) (sat_nil p)))
def c860 : List Lit := [(67, true), (63, false), (3, true)]
theorem step860 (p : Nat → Bool) (h : Constraints p) : clause p c860 = true :=
  Snake9.LocalRup.prove_clause [c239, c157] c860 (by decide) p (sat_cons (step239 p h) (sat_cons (step157 p h) (sat_nil p)))
def c861 : List Lit := [(64, true), (63, false), (3, true)]
theorem step861 (p : Nat → Bool) (h : Constraints p) : clause p c861 = true :=
  Snake9.LocalRup.prove_clause [c239, c158] c861 (by decide) p (sat_cons (step239 p h) (sat_cons (step158 p h) (sat_nil p)))
def c862 : List Lit := [(65, false), (72, true), (69, true)]
theorem step862 (p : Nat → Bool) (h : Constraints p) : clause p c862 = true :=
  Snake9.LocalRup.prove_clause [c240, c163] c862 (by decide) p (sat_cons (step240 p h) (sat_cons (step163 p h) (sat_nil p)))
def c863 : List Lit := [(65, false), (69, true), (66, true)]
theorem step863 (p : Nat → Bool) (h : Constraints p) : clause p c863 = true :=
  Snake9.LocalRup.prove_clause [c240, c165] c863 (by decide) p (sat_cons (step240 p h) (sat_cons (step165 p h) (sat_nil p)))
def c864 : List Lit := [(70, false), (69, true)]
theorem step864 (p : Nat → Bool) (h : Constraints p) : clause p c864 = true :=
  Snake9.LocalRup.prove_clause [c241, c175] c864 (by decide) p (sat_cons (step241 p h) (sat_cons (step175 p h) (sat_nil p)))
def c865 : List Lit := [(70, false), (67, true)]
theorem step865 (p : Nat → Bool) (h : Constraints p) : clause p c865 = true :=
  Snake9.LocalRup.prove_clause [c241, c176] c865 (by decide) p (sat_cons (step241 p h) (sat_cons (step176 p h) (sat_nil p)))
def c866 : List Lit := [(74, true), (73, false), (66, true)]
theorem step866 (p : Nat → Bool) (h : Constraints p) : clause p c866 = true :=
  Snake9.LocalRup.prove_clause [c242, c182] c866 (by decide) p (sat_cons (step242 p h) (sat_cons (step182 p h) (sat_nil p)))
def c867 : List Lit := [(72, true), (73, false), (66, true)]
theorem step867 (p : Nat → Bool) (h : Constraints p) : clause p c867 = true :=
  Snake9.LocalRup.prove_clause [c242, c183] c867 (by decide) p (sat_cons (step242 p h) (sat_cons (step183 p h) (sat_nil p)))
def c868 : List Lit := [(76, false), (78, true)]
theorem step868 (p : Nat → Bool) (h : Constraints p) : clause p c868 = true :=
  Snake9.LocalRup.prove_clause [c243, c188] c868 (by decide) p (sat_cons (step243 p h) (sat_cons (step188 p h) (sat_nil p)))
def c869 : List Lit := [(76, false), (75, true)]
theorem step869 (p : Nat → Bool) (h : Constraints p) : clause p c869 = true :=
  Snake9.LocalRup.prove_clause [c243, c189] c869 (by decide) p (sat_cons (step243 p h) (sat_cons (step189 p h) (sat_nil p)))
def c870 : List Lit := [(83, false), (84, true)]
theorem step870 (p : Nat → Bool) (h : Constraints p) : clause p c870 = true :=
  Snake9.LocalRup.prove_clause [c247, c199] c870 (by decide) p (sat_cons (step247 p h) (sat_cons (step199 p h) (sat_nil p)))
def c871 : List Lit := [(83, false), (82, true)]
theorem step871 (p : Nat → Bool) (h : Constraints p) : clause p c871 = true :=
  Snake9.LocalRup.prove_clause [c247, c200] c871 (by decide) p (sat_cons (step247 p h) (sat_cons (step200 p h) (sat_nil p)))
def c872 : List Lit := [(40, true), (82, true), (88, false)]
theorem step872 (p : Nat → Bool) (h : Constraints p) : clause p c872 = true :=
  Snake9.LocalRup.prove_clause [c248, c204] c872 (by decide) p (sat_cons (step248 p h) (sat_cons (step204 p h) (sat_nil p)))
def c873 : List Lit := [(95, false), (96, true)]
theorem step873 (p : Nat → Bool) (h : Constraints p) : clause p c873 = true :=
  Snake9.LocalRup.prove_clause [c250, c208] c873 (by decide) p (sat_cons (step250 p h) (sat_cons (step208 p h) (sat_nil p)))
def c874 : List Lit := [(108, false), (107, true)]
theorem step874 (p : Nat → Bool) (h : Constraints p) : clause p c874 = true :=
  Snake9.LocalRup.prove_clause [c251, c213] c874 (by decide) p (sat_cons (step251 p h) (sat_cons (step213 p h) (sat_nil p)))
def c875 : List Lit := [(112, false), (113, false)]
theorem step875 (p : Nat → Bool) (h : Constraints p) : clause p c875 = true :=
  Snake9.LocalRup.prove_clause [c739, c255] c875 (by decide) p (sat_cons (step739 p h) (sat_cons (step255 p h) (sat_nil p)))
def c876 : List Lit := [(233, false), (239, false)]
theorem step876 (p : Nat → Bool) (h : Constraints p) : clause p c876 = true :=
  Snake9.LocalRup.prove_clause [c730, c269] c876 (by decide) p (sat_cons (step730 p h) (sat_cons (step269 p h) (sat_nil p)))
def c877 : List Lit := [(229, false), (241, false)]
theorem step877 (p : Nat → Bool) (h : Constraints p) : clause p c877 = true :=
  Snake9.LocalRup.prove_clause [c725, c273] c877 (by decide) p (sat_cons (step725 p h) (sat_cons (step273 p h) (sat_nil p)))
def c878 : List Lit := [(124, false), (245, false)]
theorem step878 (p : Nat → Bool) (h : Constraints p) : clause p c878 = true :=
  Snake9.LocalRup.prove_clause [c735, c278] c878 (by decide) p (sat_cons (step735 p h) (sat_cons (step278 p h) (sat_nil p)))
def c879 : List Lit := [(243, false), (269, false)]
theorem step879 (p : Nat → Bool) (h : Constraints p) : clause p c879 = true :=
  Snake9.LocalRup.prove_clause [c721, c294] c879 (by decide) p (sat_cons (step721 p h) (sat_cons (step294 p h) (sat_nil p)))
def c880 : List Lit := [(275, false), (279, false)]
theorem step880 (p : Nat → Bool) (h : Constraints p) : clause p c880 = true :=
  Snake9.LocalRup.prove_clause [c728, c300] c880 (by decide) p (sat_cons (step728 p h) (sat_cons (step300 p h) (sat_nil p)))
def c881 : List Lit := [(271, false), (323, false)]
theorem step881 (p : Nat → Bool) (h : Constraints p) : clause p c881 = true :=
  Snake9.LocalRup.prove_clause [c717, c312] c881 (by decide) p (sat_cons (step717 p h) (sat_cons (step312 p h) (sat_nil p)))
def c882 : List Lit := [(349, false), (375, false)]
theorem step882 (p : Nat → Bool) (h : Constraints p) : clause p c882 = true :=
  Snake9.LocalRup.prove_clause [c719, c335] c882 (by decide) p (sat_cons (step719 p h) (sat_cons (step335 p h) (sat_nil p)))
def c883 : List Lit := [(377, false), (431, false)]
theorem step883 (p : Nat → Bool) (h : Constraints p) : clause p c883 = true :=
  Snake9.LocalRup.prove_clause [c716, c352] c883 (by decide) p (sat_cons (step716 p h) (sat_cons (step352 p h) (sat_nil p)))
def c884 : List Lit := [(325, false), (433, false)]
theorem step884 (p : Nat → Bool) (h : Constraints p) : clause p c884 = true :=
  Snake9.LocalRup.prove_clause [c357, c355] c884 (by decide) p (sat_cons (step357 p h) (sat_cons (step355 p h) (sat_nil p)))
def c885 : List Lit := [(826, false), (854, true)]
theorem step885 (p : Nat → Bool) (h : Constraints p) : clause p c885 = true :=
  Snake9.LocalRup.prove_clause [c796, c481] c885 (by decide) p (sat_cons (step796 p h) (sat_cons (step481 p h) (sat_nil p)))
def c886 : List Lit := [(827, false), (855, true)]
theorem step886 (p : Nat → Bool) (h : Constraints p) : clause p c886 = true :=
  Snake9.LocalRup.prove_clause [c796, c483] c886 (by decide) p (sat_cons (step796 p h) (sat_cons (step483 p h) (sat_nil p)))
def c887 : List Lit := [(872, true), (801, false)]
theorem step887 (p : Nat → Bool) (h : Constraints p) : clause p c887 = true :=
  Snake9.LocalRup.prove_clause [c797, c484] c887 (by decide) p (sat_cons (step797 p h) (sat_cons (step484 p h) (sat_nil p)))
def c888 : List Lit := [(873, true), (802, false)]
theorem step888 (p : Nat → Bool) (h : Constraints p) : clause p c888 = true :=
  Snake9.LocalRup.prove_clause [c797, c487] c888 (by decide) p (sat_cons (step797 p h) (sat_cons (step487 p h) (sat_nil p)))
def c889 : List Lit := [(874, true), (803, false)]
theorem step889 (p : Nat → Bool) (h : Constraints p) : clause p c889 = true :=
  Snake9.LocalRup.prove_clause [c797, c491] c889 (by decide) p (sat_cons (step797 p h) (sat_cons (step491 p h) (sat_nil p)))
def c890 : List Lit := [(875, true), (804, false)]
theorem step890 (p : Nat → Bool) (h : Constraints p) : clause p c890 = true :=
  Snake9.LocalRup.prove_clause [c797, c493] c890 (by decide) p (sat_cons (step797 p h) (sat_cons (step493 p h) (sat_nil p)))
def c891 : List Lit := [(950, false), (982, true)]
theorem step891 (p : Nat → Bool) (h : Constraints p) : clause p c891 = true :=
  Snake9.LocalRup.prove_clause [c799, c581] c891 (by decide) p (sat_cons (step799 p h) (sat_cons (step581 p h) (sat_nil p)))
def c892 : List Lit := [(951, false), (983, true)]
theorem step892 (p : Nat → Bool) (h : Constraints p) : clause p c892 = true :=
  Snake9.LocalRup.prove_clause [c799, c582] c892 (by decide) p (sat_cons (step799 p h) (sat_cons (step582 p h) (sat_nil p)))
def c893 : List Lit := [(998, true), (923, false)]
theorem step893 (p : Nat → Bool) (h : Constraints p) : clause p c893 = true :=
  Snake9.LocalRup.prove_clause [c800, c583] c893 (by decide) p (sat_cons (step800 p h) (sat_cons (step583 p h) (sat_nil p)))
def c894 : List Lit := [(999, true), (924, false)]
theorem step894 (p : Nat → Bool) (h : Constraints p) : clause p c894 = true :=
  Snake9.LocalRup.prove_clause [c800, c585] c894 (by decide) p (sat_cons (step800 p h) (sat_cons (step585 p h) (sat_nil p)))
def c895 : List Lit := [(1000, true), (925, false)]
theorem step895 (p : Nat → Bool) (h : Constraints p) : clause p c895 = true :=
  Snake9.LocalRup.prove_clause [c800, c588] c895 (by decide) p (sat_cons (step800 p h) (sat_cons (step588 p h) (sat_nil p)))
def c896 : List Lit := [(926, false), (1001, true)]
theorem step896 (p : Nat → Bool) (h : Constraints p) : clause p c896 = true :=
  Snake9.LocalRup.prove_clause [c800, c591] c896 (by decide) p (sat_cons (step800 p h) (sat_cons (step591 p h) (sat_nil p)))
def c897 : List Lit := [(927, false), (1002, true)]
theorem step897 (p : Nat → Bool) (h : Constraints p) : clause p c897 = true :=
  Snake9.LocalRup.prove_clause [c800, c593] c897 (by decide) p (sat_cons (step800 p h) (sat_cons (step593 p h) (sat_nil p)))
def c898 : List Lit := [(928, false), (1003, true)]
theorem step898 (p : Nat → Bool) (h : Constraints p) : clause p c898 = true :=
  Snake9.LocalRup.prove_clause [c800, c595] c898 (by decide) p (sat_cons (step800 p h) (sat_cons (step595 p h) (sat_nil p)))
def c899 : List Lit := [(872, false), (1003, false)]
theorem step899 (p : Nat → Bool) (h : Constraints p) : clause p c899 = true :=
  Snake9.LocalRup.prove_clause [c602, c596] c899 (by decide) p (sat_cons (step602 p h) (sat_cons (step596 p h) (sat_nil p)))
def c900 : List Lit := [(873, false), (1002, false)]
theorem step900 (p : Nat → Bool) (h : Constraints p) : clause p c900 = true :=
  Snake9.LocalRup.prove_clause [c602, c597] c900 (by decide) p (sat_cons (step602 p h) (sat_cons (step597 p h) (sat_nil p)))
def c901 : List Lit := [(874, false), (1001, false)]
theorem step901 (p : Nat → Bool) (h : Constraints p) : clause p c901 = true :=
  Snake9.LocalRup.prove_clause [c602, c598] c901 (by decide) p (sat_cons (step602 p h) (sat_cons (step598 p h) (sat_nil p)))
def c902 : List Lit := [(875, false), (1000, false)]
theorem step902 (p : Nat → Bool) (h : Constraints p) : clause p c902 = true :=
  Snake9.LocalRup.prove_clause [c602, c599] c902 (by decide) p (sat_cons (step602 p h) (sat_cons (step599 p h) (sat_nil p)))
end B112E123
