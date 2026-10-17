import B112E145Inputs
namespace B112E145
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c699 : List Lit := [(31, false), (28, false), (34, false)]
theorem step699 (p : Nat → Bool) (h : Constraints p) : clause p c699 = true :=
  Snake9.LocalRup.prove_clause [c67, c93] c699 (by decide) p (sat_cons (step67 p h) (sat_cons (step93 p h) (sat_nil p)))
def c700 : List Lit := [(56, false)]
theorem step700 (p : Nat → Bool) (h : Constraints p) : clause p c700 = true :=
  Snake9.LocalRup.prove_clause [c202, c130] c700 (by decide) p (sat_cons (step202 p h) (sat_cons (step130 p h) (sat_nil p)))
def c701 : List Lit := [(62, false)]
theorem step701 (p : Nat → Bool) (h : Constraints p) : clause p c701 = true :=
  Snake9.LocalRup.prove_clause [c205, c135] c701 (by decide) p (sat_cons (step205 p h) (sat_cons (step135 p h) (sat_nil p)))
def c702 : List Lit := [(410, false)]
theorem step702 (p : Nat → Bool) (h : Constraints p) : clause p c702 = true :=
  Snake9.LocalRup.prove_clause [c424, c421] c702 (by decide) p (sat_cons (step424 p h) (sat_cons (step421 p h) (sat_nil p)))
def c703 : List Lit := [(308, false)]
theorem step703 (p : Nat → Bool) (h : Constraints p) : clause p c703 = true :=
  Snake9.LocalRup.prove_clause [c424, c423] c703 (by decide) p (sat_cons (step424 p h) (sat_cons (step423 p h) (sat_nil p)))
def c704 : List Lit := [(408, false)]
theorem step704 (p : Nat → Bool) (h : Constraints p) : clause p c704 = true :=
  Snake9.LocalRup.prove_clause [c702, c418] c704 (by decide) p (sat_cons (step702 p h) (sat_cons (step418 p h) (sat_nil p)))
def c705 : List Lit := [(358, false)]
theorem step705 (p : Nat → Bool) (h : Constraints p) : clause p c705 = true :=
  Snake9.LocalRup.prove_clause [c702, c420] c705 (by decide) p (sat_cons (step702 p h) (sat_cons (step420 p h) (sat_nil p)))
def c706 : List Lit := [(306, false)]
theorem step706 (p : Nat → Bool) (h : Constraints p) : clause p c706 = true :=
  Snake9.LocalRup.prove_clause [c703, c326] c706 (by decide) p (sat_cons (step703 p h) (sat_cons (step326 p h) (sat_nil p)))
def c707 : List Lit := [(256, false)]
theorem step707 (p : Nat → Bool) (h : Constraints p) : clause p c707 = true :=
  Snake9.LocalRup.prove_clause [c703, c329] c707 (by decide) p (sat_cons (step703 p h) (sat_cons (step329 p h) (sat_nil p)))
def c708 : List Lit := [(406, false)]
theorem step708 (p : Nat → Bool) (h : Constraints p) : clause p c708 = true :=
  Snake9.LocalRup.prove_clause [c704, c414] c708 (by decide) p (sat_cons (step704 p h) (sat_cons (step414 p h) (sat_nil p)))
def c709 : List Lit := [(382, false)]
theorem step709 (p : Nat → Bool) (h : Constraints p) : clause p c709 = true :=
  Snake9.LocalRup.prove_clause [c704, c416] c709 (by decide) p (sat_cons (step704 p h) (sat_cons (step416 p h) (sat_nil p)))
def c710 : List Lit := [(356, false)]
theorem step710 (p : Nat → Bool) (h : Constraints p) : clause p c710 = true :=
  Snake9.LocalRup.prove_clause [c705, c372] c710 (by decide) p (sat_cons (step705 p h) (sat_cons (step372 p h) (sat_nil p)))
def c711 : List Lit := [(332, false)]
theorem step711 (p : Nat → Bool) (h : Constraints p) : clause p c711 = true :=
  Snake9.LocalRup.prove_clause [c705, c374] c711 (by decide) p (sat_cons (step705 p h) (sat_cons (step374 p h) (sat_nil p)))
def c712 : List Lit := [(304, false)]
theorem step712 (p : Nat → Bool) (h : Constraints p) : clause p c712 = true :=
  Snake9.LocalRup.prove_clause [c706, c321] c712 (by decide) p (sat_cons (step706 p h) (sat_cons (step321 p h) (sat_nil p)))
def c713 : List Lit := [(280, false)]
theorem step713 (p : Nat → Bool) (h : Constraints p) : clause p c713 = true :=
  Snake9.LocalRup.prove_clause [c706, c324] c713 (by decide) p (sat_cons (step706 p h) (sat_cons (step324 p h) (sat_nil p)))
def c714 : List Lit := [(254, false)]
theorem step714 (p : Nat → Bool) (h : Constraints p) : clause p c714 = true :=
  Snake9.LocalRup.prove_clause [c707, c275] c714 (by decide) p (sat_cons (step707 p h) (sat_cons (step275 p h) (sat_nil p)))
def c715 : List Lit := [(230, false)]
theorem step715 (p : Nat → Bool) (h : Constraints p) : clause p c715 = true :=
  Snake9.LocalRup.prove_clause [c707, c278] c715 (by decide) p (sat_cons (step707 p h) (sat_cons (step278 p h) (sat_nil p)))
def c716 : List Lit := [(404, false)]
theorem step716 (p : Nat → Bool) (h : Constraints p) : clause p c716 = true :=
  Snake9.LocalRup.prove_clause [c708, c411] c716 (by decide) p (sat_cons (step708 p h) (sat_cons (step411 p h) (sat_nil p)))
def c717 : List Lit := [(380, false)]
theorem step717 (p : Nat → Bool) (h : Constraints p) : clause p c717 = true :=
  Snake9.LocalRup.prove_clause [c709, c391] c717 (by decide) p (sat_cons (step709 p h) (sat_cons (step391 p h) (sat_nil p)))
def c718 : List Lit := [(342, false)]
theorem step718 (p : Nat → Bool) (h : Constraints p) : clause p c718 = true :=
  Snake9.LocalRup.prove_clause [c710, c370] c718 (by decide) p (sat_cons (step710 p h) (sat_cons (step370 p h) (sat_nil p)))
def c719 : List Lit := [(318, false)]
theorem step719 (p : Nat → Bool) (h : Constraints p) : clause p c719 = true :=
  Snake9.LocalRup.prove_clause [c711, c350] c719 (by decide) p (sat_cons (step711 p h) (sat_cons (step350 p h) (sat_nil p)))
def c720 : List Lit := [(290, false)]
theorem step720 (p : Nat → Bool) (h : Constraints p) : clause p c720 = true :=
  Snake9.LocalRup.prove_clause [c712, c319] c720 (by decide) p (sat_cons (step712 p h) (sat_cons (step319 p h) (sat_nil p)))
def c721 : List Lit := [(266, false)]
theorem step721 (p : Nat → Bool) (h : Constraints p) : clause p c721 = true :=
  Snake9.LocalRup.prove_clause [c713, c299] c721 (by decide) p (sat_cons (step713 p h) (sat_cons (step299 p h) (sat_nil p)))
def c722 : List Lit := [(252, false)]
theorem step722 (p : Nat → Bool) (h : Constraints p) : clause p c722 = true :=
  Snake9.LocalRup.prove_clause [c714, c270] c722 (by decide) p (sat_cons (step714 p h) (sat_cons (step270 p h) (sat_nil p)))
def c723 : List Lit := [(240, false)]
theorem step723 (p : Nat → Bool) (h : Constraints p) : clause p c723 = true :=
  Snake9.LocalRup.prove_clause [c714, c273] c723 (by decide) p (sat_cons (step714 p h) (sat_cons (step273 p h) (sat_nil p)))
def c724 : List Lit := [(228, false)]
theorem step724 (p : Nat → Bool) (h : Constraints p) : clause p c724 = true :=
  Snake9.LocalRup.prove_clause [c715, c244] c724 (by decide) p (sat_cons (step715 p h) (sat_cons (step244 p h) (sat_nil p)))
def c725 : List Lit := [(218, false)]
theorem step725 (p : Nat → Bool) (h : Constraints p) : clause p c725 = true :=
  Snake9.LocalRup.prove_clause [c715, c247] c725 (by decide) p (sat_cons (step715 p h) (sat_cons (step247 p h) (sat_nil p)))
def c726 : List Lit := [(402, false)]
theorem step726 (p : Nat → Bool) (h : Constraints p) : clause p c726 = true :=
  Snake9.LocalRup.prove_clause [c716, c408] c726 (by decide) p (sat_cons (step716 p h) (sat_cons (step408 p h) (sat_nil p)))
def c727 : List Lit := [(372, false)]
theorem step727 (p : Nat → Bool) (h : Constraints p) : clause p c727 = true :=
  Snake9.LocalRup.prove_clause [c717, c389] c727 (by decide) p (sat_cons (step717 p h) (sat_cons (step389 p h) (sat_nil p)))
def c728 : List Lit := [(316, false)]
theorem step728 (p : Nat → Bool) (h : Constraints p) : clause p c728 = true :=
  Snake9.LocalRup.prove_clause [c719, c339] c728 (by decide) p (sat_cons (step719 p h) (sat_cons (step339 p h) (sat_nil p)))
def c729 : List Lit := [(288, false)]
theorem step729 (p : Nat → Bool) (h : Constraints p) : clause p c729 = true :=
  Snake9.LocalRup.prove_clause [c720, c308] c729 (by decide) p (sat_cons (step720 p h) (sat_cons (step308 p h) (sat_nil p)))
def c730 : List Lit := [(264, false)]
theorem step730 (p : Nat → Bool) (h : Constraints p) : clause p c730 = true :=
  Snake9.LocalRup.prove_clause [c721, c288] c730 (by decide) p (sat_cons (step721 p h) (sat_cons (step288 p h) (sat_nil p)))
def c731 : List Lit := [(238, false)]
theorem step731 (p : Nat → Bool) (h : Constraints p) : clause p c731 = true :=
  Snake9.LocalRup.prove_clause [c723, c256] c731 (by decide) p (sat_cons (step723 p h) (sat_cons (step256 p h) (sat_nil p)))
def c732 : List Lit := [(222, false)]
theorem step732 (p : Nat → Bool) (h : Constraints p) : clause p c732 = true :=
  Snake9.LocalRup.prove_clause [c724, c242] c732 (by decide) p (sat_cons (step724 p h) (sat_cons (step242 p h) (sat_nil p)))
def c733 : List Lit := [(398, false)]
theorem step733 (p : Nat → Bool) (h : Constraints p) : clause p c733 = true :=
  Snake9.LocalRup.prove_clause [c726, c406] c733 (by decide) p (sat_cons (step726 p h) (sat_cons (step406 p h) (sat_nil p)))
def c734 : List Lit := [(314, false)]
theorem step734 (p : Nat → Bool) (h : Constraints p) : clause p c734 = true :=
  Snake9.LocalRup.prove_clause [c728, c337] c734 (by decide) p (sat_cons (step728 p h) (sat_cons (step337 p h) (sat_nil p)))
def c735 : List Lit := [(262, false)]
theorem step735 (p : Nat → Bool) (h : Constraints p) : clause p c735 = true :=
  Snake9.LocalRup.prove_clause [c730, c285] c735 (by decide) p (sat_cons (step730 p h) (sat_cons (step285 p h) (sat_nil p)))
def c736 : List Lit := [(106, true), (110, true), (111, true), (112, true), (115, true), (117, true), (118, true), (120, true), (122, true), (125, true), (127, true), (128, true), (129, true), (133, true), (134, true), (135, true), (136, true), (139, true), (142, true), (145, true), (146, true), (147, true), (149, true), (151, true), (154, true), (157, true), (159, true), (161, true), (162, true), (163, true), (167, true), (169, true), (171, true), (173, true), (175, true), (178, true), (180, true), (181, true), (183, true), (187, true), (188, true), (189, true), (190, true), (194, true), (196, true), (197, true), (199, true), (203, true), (204, true), (205, true), (206, true)]
theorem step736 (p : Nat → Bool) (h : Constraints p) : clause p c736 = true :=
  Snake9.LocalRup.prove_clause [c175, c176, c177, c178, c179, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191, c192, c193, c194, c195, c196, c197, c198, c199, c200, c201, c202, c203, c204, c205, c206, c207, c208, c209, c210, c211, c212, c213, c214, c215, c216, c217, c218, c219, c220, c221, c222, c223, c224, c225, c226, c425] c736 (by decide) p (sat_cons (step175 p h) (sat_cons (step176 p h) (sat_cons (step177 p h) (sat_cons (step178 p h) (sat_cons (step179 p h) (sat_cons (step180 p h) (sat_cons (step181 p h) (sat_cons (step182 p h) (sat_cons (step183 p h) (sat_cons (step184 p h) (sat_cons (step185 p h) (sat_cons (step186 p h) (sat_cons (step187 p h) (sat_cons (step188 p h) (sat_cons (step189 p h) (sat_cons (step190 p h) (sat_cons (step191 p h) (sat_cons (step192 p h) (sat_cons (step193 p h) (sat_cons (step194 p h) (sat_cons (step195 p h) (sat_cons (step196 p h) (sat_cons (step197 p h) (sat_cons (step198 p h) (sat_cons (step199 p h) (sat_cons (step200 p h) (sat_cons (step201 p h) (sat_cons (step202 p h) (sat_cons (step203 p h) (sat_cons (step204 p h) (sat_cons (step205 p h) (sat_cons (step206 p h) (sat_cons (step207 p h) (sat_cons (step208 p h) (sat_cons (step209 p h) (sat_cons (step210 p h) (sat_cons (step211 p h) (sat_cons (step212 p h) (sat_cons (step213 p h) (sat_cons (step214 p h) (sat_cons (step215 p h) (sat_cons (step216 p h) (sat_cons (step217 p h) (sat_cons (step218 p h) (sat_cons (step219 p h) (sat_cons (step220 p h) (sat_cons (step221 p h) (sat_cons (step222 p h) (sat_cons (step223 p h) (sat_cons (step224 p h) (sat_cons (step225 p h) (sat_cons (step226 p h) (sat_cons (step425 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c737 : List Lit := [(820, true)]
theorem step737 (p : Nat → Bool) (h : Constraints p) : clause p c737 = true :=
  Snake9.LocalRup.prove_clause [c700, c447] c737 (by decide) p (sat_cons (step700 p h) (sat_cons (step447 p h) (sat_nil p)))
def c738 : List Lit := [(822, true)]
theorem step738 (p : Nat → Bool) (h : Constraints p) : clause p c738 = true :=
  Snake9.LocalRup.prove_clause [c737, c448] c738 (by decide) p (sat_cons (step737 p h) (sat_cons (step448 p h) (sat_nil p)))
def c739 : List Lit := [(825, true)]
theorem step739 (p : Nat → Bool) (h : Constraints p) : clause p c739 = true :=
  Snake9.LocalRup.prove_clause [c701, c449] c739 (by decide) p (sat_cons (step701 p h) (sat_cons (step449 p h) (sat_nil p)))
def c740 : List Lit := [(827, true)]
theorem step740 (p : Nat → Bool) (h : Constraints p) : clause p c740 = true :=
  Snake9.LocalRup.prove_clause [c739, c450] c740 (by decide) p (sat_cons (step739 p h) (sat_cons (step450 p h) (sat_nil p)))
def c741 : List Lit := [(831, true)]
theorem step741 (p : Nat → Bool) (h : Constraints p) : clause p c741 = true :=
  Snake9.LocalRup.prove_clause [c738, c740, c451] c741 (by decide) p (sat_cons (step738 p h) (sat_cons (step740 p h) (sat_cons (step451 p h) (sat_nil p))))
def c742 : List Lit := [(850, false), (859, true)]
theorem step742 (p : Nat → Bool) (h : Constraints p) : clause p c742 = true :=
  Snake9.LocalRup.prove_clause [c741, c457] c742 (by decide) p (sat_cons (step741 p h) (sat_cons (step457 p h) (sat_nil p)))
def c743 : List Lit := [(57, false), (59, false), (58, false)]
theorem step743 (p : Nat → Bool) (h : Constraints p) : clause p c743 = true :=
  Snake9.LocalRup.prove_clause [c734, c134, c133, c131, c335] c743 (by decide) p (sat_cons (step734 p h) (sat_cons (step134 p h) (sat_cons (step133 p h) (sat_cons (step131 p h) (sat_cons (step335 p h) (sat_nil p))))))
def c744 : List Lit := [(1343, true)]
theorem step744 (p : Nat → Bool) (h : Constraints p) : clause p c744 = true :=
  Snake9.LocalRup.prove_clause [c618, c619, c616, c617, c611, c615, c609, c743] c744 (by decide) p (sat_cons (step618 p h) (sat_cons (step619 p h) (sat_cons (step616 p h) (sat_cons (step617 p h) (sat_cons (step611 p h) (sat_cons (step615 p h) (sat_cons (step609 p h) (sat_cons (step743 p h) (sat_nil p)))))))))
def c745 : List Lit := [(1369, true)]
theorem step745 (p : Nat → Bool) (h : Constraints p) : clause p c745 = true :=
  Snake9.LocalRup.prove_clause [c744, c648] c745 (by decide) p (sat_cons (step744 p h) (sat_cons (step648 p h) (sat_nil p)))
def c746 : List Lit := [(1362, true), (175, true)]
theorem step746 (p : Nat → Bool) (h : Constraints p) : clause p c746 = true :=
  Snake9.LocalRup.prove_clause [c640, c641, c636, c637, c626, c634, c632, c624, c152, c147] c746 (by decide) p (sat_cons (step640 p h) (sat_cons (step641 p h) (sat_cons (step636 p h) (sat_cons (step637 p h) (sat_cons (step626 p h) (sat_cons (step634 p h) (sat_cons (step632 p h) (sat_cons (step624 p h) (sat_cons (step152 p h) (sat_cons (step147 p h) (sat_nil p)))))))))))
def c747 : List Lit := [(24, true), (253, true), (1259, true)]
theorem step747 (p : Nat → Bool) (h : Constraints p) : clause p c747 = true :=
  Snake9.LocalRup.prove_clause [c184, c271, c257, c249, c248, c269, c267, c260, c259, c505, c496, c499, c502, c507, c72, c491, c493, c70, c489, c35, c51] c747 (by decide) p (sat_cons (step184 p h) (sat_cons (step271 p h) (sat_cons (step257 p h) (sat_cons (step249 p h) (sat_cons (step248 p h) (sat_cons (step269 p h) (sat_cons (step267 p h) (sat_cons (step260 p h) (sat_cons (step259 p h) (sat_cons (step505 p h) (sat_cons (step496 p h) (sat_cons (step499 p h) (sat_cons (step502 p h) (sat_cons (step507 p h) (sat_cons (step72 p h) (sat_cons (step491 p h) (sat_cons (step493 p h) (sat_cons (step70 p h) (sat_cons (step489 p h) (sat_cons (step35 p h) (sat_cons (step51 p h) (sat_nil p))))))))))))))))))))))
def c748 : List Lit := [(1304, true)]
theorem step748 (p : Nat → Bool) (h : Constraints p) : clause p c748 = true :=
  Snake9.LocalRup.prove_clause [c577, c579, c574, c563, c565, c568, c569, c560, c561, c107, c122, c117, c120] c748 (by decide) p (sat_cons (step577 p h) (sat_cons (step579 p h) (sat_cons (step574 p h) (sat_cons (step563 p h) (sat_cons (step565 p h) (sat_cons (step568 p h) (sat_cons (step569 p h) (sat_cons (step560 p h) (sat_cons (step561 p h) (sat_cons (step107 p h) (sat_cons (step122 p h) (sat_cons (step117 p h) (sat_cons (step120 p h) (sat_nil p))))))))))))))
def c749 : List Lit := [(1311, true)]
theorem step749 (p : Nat → Bool) (h : Constraints p) : clause p c749 = true :=
  Snake9.LocalRup.prove_clause [c748, c584] c749 (by decide) p (sat_cons (step748 p h) (sat_cons (step584 p h) (sat_nil p)))
def c750 : List Lit := [(21, false), (24, false), (8, false)]
theorem step750 (p : Nat → Bool) (h : Constraints p) : clause p c750 = true :=
  Snake9.LocalRup.prove_clause [c722, c69, c72, c77, c259, c261, c260, c265, c268] c750 (by decide) p (sat_cons (step722 p h) (sat_cons (step69 p h) (sat_cons (step72 p h) (sat_cons (step77 p h) (sat_cons (step259 p h) (sat_cons (step261 p h) (sat_cons (step260 p h) (sat_cons (step265 p h) (sat_cons (step268 p h) (sat_nil p))))))))))
def c751 : List Lit := [(20, true), (24, false), (1242, true), (8, false)]
theorem step751 (p : Nat → Bool) (h : Constraints p) : clause p c751 = true :=
  Snake9.LocalRup.prove_clause [c714, c707, c477, c472, c469, c470, c31, c480, c464, c461, c77, c261, c265, c266, c269, c272, c277, c257, c243, c250, c241, c48, c235, c236, c234, c24, c29, c39] c751 (by decide) p (sat_cons (step714 p h) (sat_cons (step707 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step31 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step77 p h) (sat_cons (step261 p h) (sat_cons (step265 p h) (sat_cons (step266 p h) (sat_cons (step269 p h) (sat_cons (step272 p h) (sat_cons (step277 p h) (sat_cons (step257 p h) (sat_cons (step243 p h) (sat_cons (step250 p h) (sat_cons (step241 p h) (sat_cons (step48 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step234 p h) (sat_cons (step24 p h) (sat_cons (step29 p h) (sat_cons (step39 p h) (sat_nil p)))))))))))))))))))))))))))))
def c752 : List Lit := [(251, false), (21, true), (1242, true), (8, false)]
theorem step752 (p : Nat → Bool) (h : Constraints p) : clause p c752 = true :=
  Snake9.TreeRup.prove_clause [c68, c187, c714, c707, c703, c744, c748, c695, c501, c82, c477, c472, c469, c470, c31, c66, c480, c464, c461, c466, c269, c272, c274, c277, c255, c257, c328, c243, c245, c252, c253, c250, c322, c241, c232, c251, c48, c298, c236, c228, c52, c289, c24, c227, c280, c39, c41, c12, c10, c279, c58, c64, c1, c2, c88, c490, c545, c625, c539, c495, c551, c627, c541, c513, c643, c556, c517, c650, c590, c682, c601, c693] c752 (by decide) p (sat_cons (step68 p h) (sat_cons (step187 p h) (sat_cons (step714 p h) (sat_cons (step707 p h) (sat_cons (step703 p h) (sat_cons (step744 p h) (sat_cons (step748 p h) (sat_cons (step695 p h) (sat_cons (step501 p h) (sat_cons (step82 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step31 p h) (sat_cons (step66 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step466 p h) (sat_cons (step269 p h) (sat_cons (step272 p h) (sat_cons (step274 p h) (sat_cons (step277 p h) (sat_cons (step255 p h) (sat_cons (step257 p h) (sat_cons (step328 p h) (sat_cons (step243 p h) (sat_cons (step245 p h) (sat_cons (step252 p h) (sat_cons (step253 p h) (sat_cons (step250 p h) (sat_cons (step322 p h) (sat_cons (step241 p h) (sat_cons (step232 p h) (sat_cons (step251 p h) (sat_cons (step48 p h) (sat_cons (step298 p h) (sat_cons (step236 p h) (sat_cons (step228 p h) (sat_cons (step52 p h) (sat_cons (step289 p h) (sat_cons (step24 p h) (sat_cons (step227 p h) (sat_cons (step280 p h) (sat_cons (step39 p h) (sat_cons (step41 p h) (sat_cons (step12 p h) (sat_cons (step10 p h) (sat_cons (step279 p h) (sat_cons (step58 p h) (sat_cons (step64 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step88 p h) (sat_cons (step490 p h) (sat_cons (step545 p h) (sat_cons (step625 p h) (sat_cons (step539 p h) (sat_cons (step495 p h) (sat_cons (step551 p h) (sat_cons (step627 p h) (sat_cons (step541 p h) (sat_cons (step513 p h) (sat_cons (step643 p h) (sat_cons (step556 p h) (sat_cons (step517 p h) (sat_cons (step650 p h) (sat_cons (step590 p h) (sat_cons (step682 p h) (sat_cons (step601 p h) (sat_cons (step693 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c753 : List Lit := [(233, true), (1260, true), (3, false), (10, true), (127, true), (21, true), (9, true), (11, false), (13, false)]
theorem step753 (p : Nat → Bool) (h : Constraints p) : clause p c753 = true :=
  Snake9.LocalRup.prove_clause [c249, c250, c248, c48, c51, c41, c42, c493, c75, c508, c497, c502] c753 (by decide) p (sat_cons (step249 p h) (sat_cons (step250 p h) (sat_cons (step248 p h) (sat_cons (step48 p h) (sat_cons (step51 p h) (sat_cons (step41 p h) (sat_cons (step42 p h) (sat_cons (step493 p h) (sat_cons (step75 p h) (sat_cons (step508 p h) (sat_cons (step497 p h) (sat_cons (step502 p h) (sat_nil p)))))))))))))
def c754 : List Lit := [(253, false), (10, true), (21, true), (1242, true), (8, false)]
theorem step754 (p : Nat → Bool) (h : Constraints p) : clause p c754 = true :=
  Snake9.TreeRup.prove_clause [c68, c187, c707, c703, c424, c210, c748, c744, c695, c723, c183, c752, c266, c265, c262, c501, c82, c477, c472, c469, c470, c31, c66, c480, c464, c461, c466, c274, c277, c327, c328, c243, c422, c322, c241, c419, c298, c235, c236, c371, c289, c234, c24, c368, c280, c30, c12, c356, c279, c1, c2, c153, c354, c88, c545, c625, c353, c539, c551, c627, c151, c541, c632, c556, c637, c590, c644, c651, c685, c692, c598, c516, c510, c492, c753, c258, c252, c253, c251, c58, c60, c490, c63] c754 (by decide) p (sat_cons (step68 p h) (sat_cons (step187 p h) (sat_cons (step707 p h) (sat_cons (step703 p h) (sat_cons (step424 p h) (sat_cons (step210 p h) (sat_cons (step748 p h) (sat_cons (step744 p h) (sat_cons (step695 p h) (sat_cons (step723 p h) (sat_cons (step183 p h) (sat_cons (step752 p h) (sat_cons (step266 p h) (sat_cons (step265 p h) (sat_cons (step262 p h) (sat_cons (step501 p h) (sat_cons (step82 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step31 p h) (sat_cons (step66 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step466 p h) (sat_cons (step274 p h) (sat_cons (step277 p h) (sat_cons (step327 p h) (sat_cons (step328 p h) (sat_cons (step243 p h) (sat_cons (step422 p h) (sat_cons (step322 p h) (sat_cons (step241 p h) (sat_cons (step419 p h) (sat_cons (step298 p h) (sat_cons (step235 p h) (sat_cons (step236 p h) (sat_cons (step371 p h) (sat_cons (step289 p h) (sat_cons (step234 p h) (sat_cons (step24 p h) (sat_cons (step368 p h) (sat_cons (step280 p h) (sat_cons (step30 p h) (sat_cons (step12 p h) (sat_cons (step356 p h) (sat_cons (step279 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step153 p h) (sat_cons (step354 p h) (sat_cons (step88 p h) (sat_cons (step545 p h) (sat_cons (step625 p h) (sat_cons (step353 p h) (sat_cons (step539 p h) (sat_cons (step551 p h) (sat_cons (step627 p h) (sat_cons (step151 p h) (sat_cons (step541 p h) (sat_cons (step632 p h) (sat_cons (step556 p h) (sat_cons (step637 p h) (sat_cons (step590 p h) (sat_cons (step644 p h) (sat_cons (step651 p h) (sat_cons (step685 p h) (sat_cons (step692 p h) (sat_cons (step598 p h) (sat_cons (step516 p h) (sat_cons (step510 p h) (sat_cons (step492 p h) (sat_cons (step753 p h) (sat_cons (step258 p h) (sat_cons (step252 p h) (sat_cons (step253 p h) (sat_cons (step251 p h) (sat_cons (step58 p h) (sat_cons (step60 p h) (sat_cons (step490 p h) (sat_cons (step63 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c755 : List Lit := [(3, false), (1252, false), (725, false), (15, false), (720, false), (127, true), (129, true), (21, true), (1242, true)]
theorem step755 (p : Nat → Bool) (h : Constraints p) : clause p c755 = true :=
  Snake9.TreeRup.prove_clause [c68, c187, c208, c210, c186, c744, c189, c695, c460, c82, c477, c472, c469, c66, c550, c480, c464, c461, c470, c12, c11, c41, c42, c144, c153, c623, c565, c430, c75, c452, c454, c626, c80, c497, c453, c455, c641, c431, c79, c502, c456, c649, c432, c98, c543, c514, c742, c679, c433, c435, c555, c518, c458, c694, c434, c436, c459, c605, c446, c437, c589, c445, c580, c443, c444, c573, c441, c442, c438, c572, c440, c439, c124] c755 (by decide) p (sat_cons (step68 p h) (sat_cons (step187 p h) (sat_cons (step208 p h) (sat_cons (step210 p h) (sat_cons (step186 p h) (sat_cons (step744 p h) (sat_cons (step189 p h) (sat_cons (step695 p h) (sat_cons (step460 p h) (sat_cons (step82 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step66 p h) (sat_cons (step550 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step470 p h) (sat_cons (step12 p h) (sat_cons (step11 p h) (sat_cons (step41 p h) (sat_cons (step42 p h) (sat_cons (step144 p h) (sat_cons (step153 p h) (sat_cons (step623 p h) (sat_cons (step565 p h) (sat_cons (step430 p h) (sat_cons (step75 p h) (sat_cons (step452 p h) (sat_cons (step454 p h) (sat_cons (step626 p h) (sat_cons (step80 p h) (sat_cons (step497 p h) (sat_cons (step453 p h) (sat_cons (step455 p h) (sat_cons (step641 p h) (sat_cons (step431 p h) (sat_cons (step79 p h) (sat_cons (step502 p h) (sat_cons (step456 p h) (sat_cons (step649 p h) (sat_cons (step432 p h) (sat_cons (step98 p h) (sat_cons (step543 p h) (sat_cons (step514 p h) (sat_cons (step742 p h) (sat_cons (step679 p h) (sat_cons (step433 p h) (sat_cons (step435 p h) (sat_cons (step555 p h) (sat_cons (step518 p h) (sat_cons (step458 p h) (sat_cons (step694 p h) (sat_cons (step434 p h) (sat_cons (step436 p h) (sat_cons (step459 p h) (sat_cons (step605 p h) (sat_cons (step446 p h) (sat_cons (step437 p h) (sat_cons (step589 p h) (sat_cons (step445 p h) (sat_cons (step580 p h) (sat_cons (step443 p h) (sat_cons (step444 p h) (sat_cons (step573 p h) (sat_cons (step441 p h) (sat_cons (step442 p h) (sat_cons (step438 p h) (sat_cons (step572 p h) (sat_cons (step440 p h) (sat_cons (step439 p h) (sat_cons (step124 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c756 : List Lit := [(10, true), (21, true), (1242, true), (8, false)]
theorem step756 (p : Nat → Bool) (h : Constraints p) : clause p c756 = true :=
  Snake9.TreeRup.prove_clause [c68, c187, c183, c732, c703, c744, c695, c188, c748, c186, c752, c266, c265, c262, c264, c263, c501, c82, c477, c472, c469, c470, c31, c66, c480, c464, c461, c466, c426, c427, c428, c754, c271, c255, c257, c252, c253, c249, c250, c251, c58, c248, c48, c60, c51, c429, c63, c490, c495, c513, c517, c755, c24, c236, c237, c241, c234, c243, c30, c276, c1, c2, c328, c545, c624, c322, c551, c626, c298, c641, c287, c289, c649, c286, c280, c679, c279, c694, c88, c602, c85, c539, c591, c559, c542, c544, c540, c79, c92, c80, c73] c756 (by decide) p (sat_cons (step68 p h) (sat_cons (step187 p h) (sat_cons (step183 p h) (sat_cons (step732 p h) (sat_cons (step703 p h) (sat_cons (step744 p h) (sat_cons (step695 p h) (sat_cons (step188 p h) (sat_cons (step748 p h) (sat_cons (step186 p h) (sat_cons (step752 p h) (sat_cons (step266 p h) (sat_cons (step265 p h) (sat_cons (step262 p h) (sat_cons (step264 p h) (sat_cons (step263 p h) (sat_cons (step501 p h) (sat_cons (step82 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step31 p h) (sat_cons (step66 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step466 p h) (sat_cons (step426 p h) (sat_cons (step427 p h) (sat_cons (step428 p h) (sat_cons (step754 p h) (sat_cons (step271 p h) (sat_cons (step255 p h) (sat_cons (step257 p h) (sat_cons (step252 p h) (sat_cons (step253 p h) (sat_cons (step249 p h) (sat_cons (step250 p h) (sat_cons (step251 p h) (sat_cons (step58 p h) (sat_cons (step248 p h) (sat_cons (step48 p h) (sat_cons (step60 p h) (sat_cons (step51 p h) (sat_cons (step429 p h) (sat_cons (step63 p h) (sat_cons (step490 p h) (sat_cons (step495 p h) (sat_cons (step513 p h) (sat_cons (step517 p h) (sat_cons (step755 p h) (sat_cons (step24 p h) (sat_cons (step236 p h) (sat_cons (step237 p h) (sat_cons (step241 p h) (sat_cons (step234 p h) (sat_cons (step243 p h) (sat_cons (step30 p h) (sat_cons (step276 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step328 p h) (sat_cons (step545 p h) (sat_cons (step624 p h) (sat_cons (step322 p h) (sat_cons (step551 p h) (sat_cons (step626 p h) (sat_cons (step298 p h) (sat_cons (step641 p h) (sat_cons (step287 p h) (sat_cons (step289 p h) (sat_cons (step649 p h) (sat_cons (step286 p h) (sat_cons (step280 p h) (sat_cons (step679 p h) (sat_cons (step279 p h) (sat_cons (step694 p h) (sat_cons (step88 p h) (sat_cons (step602 p h) (sat_cons (step85 p h) (sat_cons (step539 p h) (sat_cons (step591 p h) (sat_cons (step559 p h) (sat_cons (step542 p h) (sat_cons (step544 p h) (sat_cons (step540 p h) (sat_cons (step79 p h) (sat_cons (step92 p h) (sat_cons (step80 p h) (sat_cons (step73 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c757 : List Lit := [(24, false), (1242, true), (8, false)]
theorem step757 (p : Nat → Bool) (h : Constraints p) : clause p c757 = true :=
  Snake9.LocalRup.prove_clause [c715, c707, c477, c472, c469, c470, c31, c480, c464, c461, c466, c750, c751, c756, c27, c10, c227, c228, c232, c245, c246, c277, c241, c271, c236, c257, c24, c250, c39, c48] c757 (by decide) p (sat_cons (step715 p h) (sat_cons (step707 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step31 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step466 p h) (sat_cons (step750 p h) (sat_cons (step751 p h) (sat_cons (step756 p h) (sat_cons (step27 p h) (sat_cons (step10 p h) (sat_cons (step227 p h) (sat_cons (step228 p h) (sat_cons (step232 p h) (sat_cons (step245 p h) (sat_cons (step246 p h) (sat_cons (step277 p h) (sat_cons (step241 p h) (sat_cons (step271 p h) (sat_cons (step236 p h) (sat_cons (step257 p h) (sat_cons (step24 p h) (sat_cons (step250 p h) (sat_cons (step39 p h) (sat_cons (step48 p h) (sat_nil p)))))))))))))))))))))))))))))))
def c758 : List Lit := [(21, true), (3, false), (1242, true), (8, false)]
theorem step758 (p : Nat → Bool) (h : Constraints p) : clause p c758 = true :=
  Snake9.LocalRup.prove_clause [c68, c744, c695, c183, c186, c748, c480, c464, c461, c477, c472, c470, c12, c623, c626, c641, c649, c679, c694, c757, c469, c66, c550, c752, c756, c266, c33, c34, c40, c38, c264, c265, c60, c62, c263, c262, c490, c75, c495, c80, c498, c79, c503, c543, c515, c555, c519, c588, c607] c758 (by decide) p (sat_cons (step68 p h) (sat_cons (step744 p h) (sat_cons (step695 p h) (sat_cons (step183 p h) (sat_cons (step186 p h) (sat_cons (step748 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step470 p h) (sat_cons (step12 p h) (sat_cons (step623 p h) (sat_cons (step626 p h) (sat_cons (step641 p h) (sat_cons (step649 p h) (sat_cons (step679 p h) (sat_cons (step694 p h) (sat_cons (step757 p h) (sat_cons (step469 p h) (sat_cons (step66 p h) (sat_cons (step550 p h) (sat_cons (step752 p h) (sat_cons (step756 p h) (sat_cons (step266 p h) (sat_cons (step33 p h) (sat_cons (step34 p h) (sat_cons (step40 p h) (sat_cons (step38 p h) (sat_cons (step264 p h) (sat_cons (step265 p h) (sat_cons (step60 p h) (sat_cons (step62 p h) (sat_cons (step263 p h) (sat_cons (step262 p h) (sat_cons (step490 p h) (sat_cons (step75 p h) (sat_cons (step495 p h) (sat_cons (step80 p h) (sat_cons (step498 p h) (sat_cons (step79 p h) (sat_cons (step503 p h) (sat_cons (step543 p h) (sat_cons (step515 p h) (sat_cons (step555 p h) (sat_cons (step519 p h) (sat_cons (step588 p h) (sat_cons (step607 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))
def c759 : List Lit := [(10, false), (3, false), (1242, true), (8, false)]
theorem step759 (p : Nat → Bool) (h : Constraints p) : clause p c759 = true :=
  Snake9.LocalRup.prove_clause [c714, c707, c758, c477, c472, c469, c470, c31, c480, c466, c39, c48, c250, c257, c271, c272, c277, c267, c245, c260, c232, c259, c228, c72, c227, c27, c10] c759 (by decide) p (sat_cons (step714 p h) (sat_cons (step707 p h) (sat_cons (step758 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step469 p h) (sat_cons (step470 p h) (sat_cons (step31 p h) (sat_cons (step480 p h) (sat_cons (step466 p h) (sat_cons (step39 p h) (sat_cons (step48 p h) (sat_cons (step250 p h) (sat_cons (step257 p h) (sat_cons (step271 p h) (sat_cons (step272 p h) (sat_cons (step277 p h) (sat_cons (step267 p h) (sat_cons (step245 p h) (sat_cons (step260 p h) (sat_cons (step232 p h) (sat_cons (step259 p h) (sat_cons (step228 p h) (sat_cons (step72 p h) (sat_cons (step227 p h) (sat_cons (step27 p h) (sat_cons (step10 p h) (sat_nil p))))))))))))))))))))))))))))
def c760 : List Lit := [(117, false), (3, false), (1242, true), (8, false)]
theorem step760 (p : Nat → Bool) (h : Constraints p) : clause p c760 = true :=
  Snake9.TreeRup.prove_clause [c68, c210, c67, c723, c707, c183, c424, c748, c695, c744, c759, c480, c464, c461, c477, c472, c470, c12, c153, c757, c496, c499, c469, c31, c66, c466, c47, c250, c49, c257, c258, c271, c252, c253, c274, c277, c251, c58, c327, c243, c60, c422, c241, c63, c419, c235, c490, c371, c234, c495, c368, c30, c513, c356, c1, c2, c517, c354, c545, c625, c353, c551, c627, c151, c553, c632, c588, c637, c600, c644, c692, c651, c685] c760 (by decide) p (sat_cons (step68 p h) (sat_cons (step210 p h) (sat_cons (step67 p h) (sat_cons (step723 p h) (sat_cons (step707 p h) (sat_cons (step183 p h) (sat_cons (step424 p h) (sat_cons (step748 p h) (sat_cons (step695 p h) (sat_cons (step744 p h) (sat_cons (step759 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step470 p h) (sat_cons (step12 p h) (sat_cons (step153 p h) (sat_cons (step757 p h) (sat_cons (step496 p h) (sat_cons (step499 p h) (sat_cons (step469 p h) (sat_cons (step31 p h) (sat_cons (step66 p h) (sat_cons (step466 p h) (sat_cons (step47 p h) (sat_cons (step250 p h) (sat_cons (step49 p h) (sat_cons (step257 p h) (sat_cons (step258 p h) (sat_cons (step271 p h) (sat_cons (step252 p h) (sat_cons (step253 p h) (sat_cons (step274 p h) (sat_cons (step277 p h) (sat_cons (step251 p h) (sat_cons (step58 p h) (sat_cons (step327 p h) (sat_cons (step243 p h) (sat_cons (step60 p h) (sat_cons (step422 p h) (sat_cons (step241 p h) (sat_cons (step63 p h) (sat_cons (step419 p h) (sat_cons (step235 p h) (sat_cons (step490 p h) (sat_cons (step371 p h) (sat_cons (step234 p h) (sat_cons (step495 p h) (sat_cons (step368 p h) (sat_cons (step30 p h) (sat_cons (step513 p h) (sat_cons (step356 p h) (sat_cons (step1 p h) (sat_cons (step2 p h) (sat_cons (step517 p h) (sat_cons (step354 p h) (sat_cons (step545 p h) (sat_cons (step625 p h) (sat_cons (step353 p h) (sat_cons (step551 p h) (sat_cons (step627 p h) (sat_cons (step151 p h) (sat_cons (step553 p h) (sat_cons (step632 p h) (sat_cons (step588 p h) (sat_cons (step637 p h) (sat_cons (step600 p h) (sat_cons (step644 p h) (sat_cons (step692 p h) (sat_cons (step651 p h) (sat_cons (step685 p h) (sat_nil p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c761 : List Lit := [(265, true), (33, true), (29, false), (22, true), (31, true)]
theorem step761 (p : Nat → Bool) (h : Constraints p) : clause p c761 = true :=
  Snake9.LocalRup.prove_clause [c190, c188, c287, c289, c284, c286, c280, c281, c279, c96, c87, c100, c84, c91] c761 (by decide) p (sat_cons (step190 p h) (sat_cons (step188 p h) (sat_cons (step287 p h) (sat_cons (step289 p h) (sat_cons (step284 p h) (sat_cons (step286 p h) (sat_cons (step280 p h) (sat_cons (step281 p h) (sat_cons (step279 p h) (sat_cons (step96 p h) (sat_cons (step87 p h) (sat_cons (step100 p h) (sat_cons (step84 p h) (sat_cons (step91 p h) (sat_nil p)))))))))))))))
def c762 : List Lit := [(251, true), (3, false), (1242, true), (8, false)]
theorem step762 (p : Nat → Bool) (h : Constraints p) : clause p c762 = true :=
  Snake9.TreeRup.prove_clause [c68, c744, c695, c187, c186, c189, c703, c748, c477, c472, c470, c469, c31, c760, c48, c42, c41, c52, c759, c758, c480, c464, c461, c12, c623, c626, c641, c649, c679, c694, c757, c66, c466, c266, c267, c264, c265, c260, c263, c262, c259, c71, c81, c75, c80, c498, c79, c500, c98, c543, c761, c298, c322, c328, c274, c276, c271, c243, c255, c241, c252, c253, c235, c251, c58, c234, c64, c30, c490, c1, c495, c545, c514, c551, c518, c556, c605, c590] c762 (by decide) p (sat_cons (step68 p h) (sat_cons (step744 p h) (sat_cons (step695 p h) (sat_cons (step187 p h) (sat_cons (step186 p h) (sat_cons (step189 p h) (sat_cons (step703 p h) (sat_cons (step748 p h) (sat_cons (step477 p h) (sat_cons (step472 p h) (sat_cons (step470 p h) (sat_cons (step469 p h) (sat_cons (step31 p h) (sat_cons (step760 p h) (sat_cons (step48 p h) (sat_cons (step42 p h) (sat_cons (step41 p h) (sat_cons (step52 p h) (sat_cons (step759 p h) (sat_cons (step758 p h) (sat_cons (step480 p h) (sat_cons (step464 p h) (sat_cons (step461 p h) (sat_cons (step12 p h) (sat_cons (step623 p h) (sat_cons (step626 p h) (sat_cons (step641 p h) (sat_cons (step649 p h) (sat_cons (step679 p h) (sat_cons (step694 p h) (sat_cons (step757 p h) (sat_cons (step66 p h) (sat_cons (step466 p h) (sat_cons (step266 p h) (sat_cons (step267 p h) (sat_cons (step264 p h) (sat_cons (step265 p h) (sat_cons (step260 p h) (sat_cons (step263 p h) (sat_cons (step262 p h) (sat_cons (step259 p h) (sat_cons (step71 p h) (sat_cons (step81 p h) (sat_cons (step75 p h) (sat_cons (step80 p h) (sat_cons (step498 p h) (sat_cons (step79 p h) (sat_cons (step500 p h) (sat_cons (step98 p h) (sat_cons (step543 p h) (sat_cons (step761 p h) (sat_cons (step298 p h) (sat_cons (step322 p h) (sat_cons (step328 p h) (sat_cons (step274 p h) (sat_cons (step276 p h) (sat_cons (step271 p h) (sat_cons (step243 p h) (sat_cons (step255 p h) (sat_cons (step241 p h) (sat_cons (step252 p h) (sat_cons (step253 p h) (sat_cons (step235 p h) (sat_cons (step251 p h) (sat_cons (step58 p h) (sat_cons (step234 p h) (sat_cons (step64 p h) (sat_cons (step30 p h) (sat_cons (step490 p h) (sat_cons (step1 p h) (sat_cons (step495 p h) (sat_cons (step545 p h) (sat_cons (step514 p h) (sat_cons (step551 p h) (sat_cons (step518 p h) (sat_cons (step556 p h) (sat_cons (step605 p h) (sat_cons (step590 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end B112E145
