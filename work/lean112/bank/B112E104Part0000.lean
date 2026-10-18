import B112E104Inputs
namespace B112E104
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c1156 : List Lit := [(43, false), (36, false), (44, false)]
theorem step1156 (p : Nat → Bool) (h : Constraints p) : clause p c1156 = true :=
  Snake9.LocalRup.prove_clause [c164, c170] c1156 (by decide) p (sat_cons (step164 p h) (sat_cons (step170 p h) (sat_nil p)))
def c1157 : List Lit := [(43, false), (36, false), (45, false)]
theorem step1157 (p : Nat → Bool) (h : Constraints p) : clause p c1157 = true :=
  Snake9.LocalRup.prove_clause [c164, c171] c1157 (by decide) p (sat_cons (step164 p h) (sat_cons (step171 p h) (sat_nil p)))
def c1158 : List Lit := [(43, false), (44, false), (45, false)]
theorem step1158 (p : Nat → Bool) (h : Constraints p) : clause p c1158 = true :=
  Snake9.LocalRup.prove_clause [c164, c172] c1158 (by decide) p (sat_cons (step164 p h) (sat_cons (step172 p h) (sat_nil p)))
def c1159 : List Lit := [(161, false), (36, false)]
theorem step1159 (p : Nat → Bool) (h : Constraints p) : clause p c1159 = true :=
  Snake9.LocalRup.prove_clause [c164, c173] c1159 (by decide) p (sat_cons (step164 p h) (sat_cons (step173 p h) (sat_nil p)))
def c1160 : List Lit := [(110, false), (99, false), (111, false)]
theorem step1160 (p : Nat → Bool) (h : Constraints p) : clause p c1160 = true :=
  Snake9.LocalRup.prove_clause [c164, c434] c1160 (by decide) p (sat_cons (step164 p h) (sat_cons (step434 p h) (sat_nil p)))
def c1161 : List Lit := [(110, false), (99, false), (112, false)]
theorem step1161 (p : Nat → Bool) (h : Constraints p) : clause p c1161 = true :=
  Snake9.LocalRup.prove_clause [c164, c435] c1161 (by decide) p (sat_cons (step164 p h) (sat_cons (step435 p h) (sat_nil p)))
def c1162 : List Lit := [(110, false), (111, false), (112, false)]
theorem step1162 (p : Nat → Bool) (h : Constraints p) : clause p c1162 = true :=
  Snake9.LocalRup.prove_clause [c164, c436] c1162 (by decide) p (sat_cons (step164 p h) (sat_cons (step436 p h) (sat_nil p)))
def c1163 : List Lit := [(2, false)]
theorem step1163 (p : Nat → Bool) (h : Constraints p) : clause p c1163 = true :=
  Snake9.LocalRup.prove_clause [c505, c2] c1163 (by decide) p (sat_cons (step505 p h) (sat_cons (step2 p h) (sat_nil p)))
def c1164 : List Lit := [(4, false)]
theorem step1164 (p : Nat → Bool) (h : Constraints p) : clause p c1164 = true :=
  Snake9.LocalRup.prove_clause [c506, c7] c1164 (by decide) p (sat_cons (step506 p h) (sat_cons (step7 p h) (sat_nil p)))
def c1165 : List Lit := [(52, false)]
theorem step1165 (p : Nat → Bool) (h : Constraints p) : clause p c1165 = true :=
  Snake9.LocalRup.prove_clause [c531, c183] c1165 (by decide) p (sat_cons (step531 p h) (sat_cons (step183 p h) (sat_nil p)))
def c1166 : List Lit := [(466, false)]
theorem step1166 (p : Nat → Bool) (h : Constraints p) : clause p c1166 = true :=
  Snake9.LocalRup.prove_clause [c746, c743] c1166 (by decide) p (sat_cons (step746 p h) (sat_cons (step743 p h) (sat_nil p)))
def c1167 : List Lit := [(350, false)]
theorem step1167 (p : Nat → Bool) (h : Constraints p) : clause p c1167 = true :=
  Snake9.LocalRup.prove_clause [c746, c745] c1167 (by decide) p (sat_cons (step746 p h) (sat_cons (step745 p h) (sat_nil p)))
def c1168 : List Lit := [(464, false)]
theorem step1168 (p : Nat → Bool) (h : Constraints p) : clause p c1168 = true :=
  Snake9.LocalRup.prove_clause [c1166, c739] c1168 (by decide) p (sat_cons (step1166 p h) (sat_cons (step739 p h) (sat_nil p)))
def c1169 : List Lit := [(406, false)]
theorem step1169 (p : Nat → Bool) (h : Constraints p) : clause p c1169 = true :=
  Snake9.LocalRup.prove_clause [c1166, c742] c1169 (by decide) p (sat_cons (step1166 p h) (sat_cons (step742 p h) (sat_nil p)))
def c1170 : List Lit := [(348, false)]
theorem step1170 (p : Nat → Bool) (h : Constraints p) : clause p c1170 = true :=
  Snake9.LocalRup.prove_clause [c1167, c641] c1170 (by decide) p (sat_cons (step1167 p h) (sat_cons (step641 p h) (sat_nil p)))
def c1171 : List Lit := [(292, false)]
theorem step1171 (p : Nat → Bool) (h : Constraints p) : clause p c1171 = true :=
  Snake9.LocalRup.prove_clause [c1167, c644] c1171 (by decide) p (sat_cons (step1167 p h) (sat_cons (step644 p h) (sat_nil p)))
def c1172 : List Lit := [(462, false)]
theorem step1172 (p : Nat → Bool) (h : Constraints p) : clause p c1172 = true :=
  Snake9.LocalRup.prove_clause [c1168, c734] c1172 (by decide) p (sat_cons (step1168 p h) (sat_cons (step734 p h) (sat_nil p)))
def c1173 : List Lit := [(434, false)]
theorem step1173 (p : Nat → Bool) (h : Constraints p) : clause p c1173 = true :=
  Snake9.LocalRup.prove_clause [c1168, c737] c1173 (by decide) p (sat_cons (step1168 p h) (sat_cons (step737 p h) (sat_nil p)))
def c1174 : List Lit := [(404, false)]
theorem step1174 (p : Nat → Bool) (h : Constraints p) : clause p c1174 = true :=
  Snake9.LocalRup.prove_clause [c1169, c691] c1174 (by decide) p (sat_cons (step1169 p h) (sat_cons (step691 p h) (sat_nil p)))
def c1175 : List Lit := [(318, false)]
theorem step1175 (p : Nat → Bool) (h : Constraints p) : clause p c1175 = true :=
  Snake9.LocalRup.prove_clause [c1170, c639] c1175 (by decide) p (sat_cons (step1170 p h) (sat_cons (step639 p h) (sat_nil p)))
def c1176 : List Lit := [(262, false)]
theorem step1176 (p : Nat → Bool) (h : Constraints p) : clause p c1176 = true :=
  Snake9.LocalRup.prove_clause [c1171, c603] c1176 (by decide) p (sat_cons (step1171 p h) (sat_cons (step603 p h) (sat_nil p)))
def c1177 : List Lit := [(460, false)]
theorem step1177 (p : Nat → Bool) (h : Constraints p) : clause p c1177 = true :=
  Snake9.LocalRup.prove_clause [c1172, c731] c1177 (by decide) p (sat_cons (step1172 p h) (sat_cons (step731 p h) (sat_nil p)))
def c1178 : List Lit := [(402, false)]
theorem step1178 (p : Nat → Bool) (h : Constraints p) : clause p c1178 = true :=
  Snake9.LocalRup.prove_clause [c1174, c687] c1178 (by decide) p (sat_cons (step1174 p h) (sat_cons (step687 p h) (sat_nil p)))
def c1179 : List Lit := [(248, false)]
theorem step1179 (p : Nat → Bool) (h : Constraints p) : clause p c1179 = true :=
  Snake9.LocalRup.prove_clause [c1176, c584] c1179 (by decide) p (sat_cons (step1176 p h) (sat_cons (step584 p h) (sat_nil p)))
def c1180 : List Lit := [(452, false)]
theorem step1180 (p : Nat → Bool) (h : Constraints p) : clause p c1180 = true :=
  Snake9.LocalRup.prove_clause [c1177, c729] c1180 (by decide) p (sat_cons (step1177 p h) (sat_cons (step729 p h) (sat_nil p)))
def c1181 : List Lit := [(400, false)]
theorem step1181 (p : Nat → Bool) (h : Constraints p) : clause p c1181 = true :=
  Snake9.LocalRup.prove_clause [c1178, c683] c1181 (by decide) p (sat_cons (step1178 p h) (sat_cons (step683 p h) (sat_nil p)))
def c1182 : List Lit := [(240, false)]
theorem step1182 (p : Nat → Bool) (h : Constraints p) : clause p c1182 = true :=
  Snake9.LocalRup.prove_clause [c1179, c573] c1182 (by decide) p (sat_cons (step1179 p h) (sat_cons (step573 p h) (sat_nil p)))
def c1183 : List Lit := [(450, false)]
theorem step1183 (p : Nat → Bool) (h : Constraints p) : clause p c1183 = true :=
  Snake9.LocalRup.prove_clause [c1180, c721] c1183 (by decide) p (sat_cons (step1180 p h) (sat_cons (step721 p h) (sat_nil p)))
def c1184 : List Lit := [(119, true), (121, true), (125, true), (128, true), (129, true), (130, true), (133, true), (134, true), (136, true), (138, true), (140, true), (144, true), (145, true), (147, true), (148, true), (150, true), (151, true), (155, true), (156, true), (160, true), (161, true), (164, true), (165, true), (169, true), (171, true), (172, true), (175, true), (176, true), (179, true), (180, true), (182, true), (184, true), (186, true), (188, true), (189, true), (192, true), (193, true), (196, true), (197, true), (199, true), (201, true), (203, true), (205, true), (206, true), (209, true), (210, true), (213, true), (214, true), (216, true), (218, true), (221, true), (222, true), (224, true), (228, true), (231, true), (232, true), (234, true), (235, true)]
theorem step1184 (p : Nat → Bool) (h : Constraints p) : clause p c1184 = true :=
  Snake9.LocalRup.prove_clause [c505, c506, c507, c508, c509, c510, c511, c512, c513, c514, c515, c516, c517, c518, c519, c520, c521, c522, c523, c524, c525, c526, c527, c528, c529, c530, c531, c532, c533, c534, c535, c536, c537, c538, c539, c540, c541, c542, c543, c544, c545, c546, c547, c548, c549, c550, c551, c552, c553, c554, c555, c556, c557, c558, c559, c560, c561, c562, c563, c747] c1184 (by decide) p (sat_cons (step505 p h) (sat_cons (step506 p h) (sat_cons (step507 p h) (sat_cons (step508 p h) (sat_cons (step509 p h) (sat_cons (step510 p h) (sat_cons (step511 p h) (sat_cons (step512 p h) (sat_cons (step513 p h) (sat_cons (step514 p h) (sat_cons (step515 p h) (sat_cons (step516 p h) (sat_cons (step517 p h) (sat_cons (step518 p h) (sat_cons (step519 p h) (sat_cons (step520 p h) (sat_cons (step521 p h) (sat_cons (step522 p h) (sat_cons (step523 p h) (sat_cons (step524 p h) (sat_cons (step525 p h) (sat_cons (step526 p h) (sat_cons (step527 p h) (sat_cons (step528 p h) (sat_cons (step529 p h) (sat_cons (step530 p h) (sat_cons (step531 p h) (sat_cons (step532 p h) (sat_cons (step533 p h) (sat_cons (step534 p h) (sat_cons (step535 p h) (sat_cons (step536 p h) (sat_cons (step537 p h) (sat_cons (step538 p h) (sat_cons (step539 p h) (sat_cons (step540 p h) (sat_cons (step541 p h) (sat_cons (step542 p h) (sat_cons (step543 p h) (sat_cons (step544 p h) (sat_cons (step545 p h) (sat_cons (step546 p h) (sat_cons (step547 p h) (sat_cons (step548 p h) (sat_cons (step549 p h) (sat_cons (step550 p h) (sat_cons (step551 p h) (sat_cons (step552 p h) (sat_cons (step553 p h) (sat_cons (step554 p h) (sat_cons (step555 p h) (sat_cons (step556 p h) (sat_cons (step557 p h) (sat_cons (step558 p h) (sat_cons (step559 p h) (sat_cons (step560 p h) (sat_cons (step561 p h) (sat_cons (step562 p h) (sat_cons (step563 p h) (sat_cons (step747 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def c1185 : List Lit := [(1413, true)]
theorem step1185 (p : Nat → Bool) (h : Constraints p) : clause p c1185 = true :=
  Snake9.LocalRup.prove_clause [c1164, c748] c1185 (by decide) p (sat_cons (step1164 p h) (sat_cons (step748 p h) (sat_nil p)))
def c1186 : List Lit := [(5, true), (1414, true)]
theorem step1186 (p : Nat → Bool) (h : Constraints p) : clause p c1186 = true :=
  Snake9.LocalRup.prove_clause [c1164, c749] c1186 (by decide) p (sat_cons (step1164 p h) (sat_cons (step749 p h) (sat_nil p)))
def c1187 : List Lit := [(1416, true)]
theorem step1187 (p : Nat → Bool) (h : Constraints p) : clause p c1187 = true :=
  Snake9.LocalRup.prove_clause [c1163, c1185, c750] c1187 (by decide) p (sat_cons (step1163 p h) (sat_cons (step1185 p h) (sat_cons (step750 p h) (sat_nil p))))
def c1188 : List Lit := [(1414, false), (1417, true)]
theorem step1188 (p : Nat → Bool) (h : Constraints p) : clause p c1188 = true :=
  Snake9.LocalRup.prove_clause [c1163, c751] c1188 (by decide) p (sat_cons (step1163 p h) (sat_cons (step751 p h) (sat_nil p)))
def c1189 : List Lit := [(1427, true)]
theorem step1189 (p : Nat → Bool) (h : Constraints p) : clause p c1189 = true :=
  Snake9.LocalRup.prove_clause [c1187, c764] c1189 (by decide) p (sat_cons (step1187 p h) (sat_cons (step764 p h) (sat_nil p)))
def c1190 : List Lit := [(1422, false), (1428, true)]
theorem step1190 (p : Nat → Bool) (h : Constraints p) : clause p c1190 = true :=
  Snake9.LocalRup.prove_clause [c1187, c765] c1190 (by decide) p (sat_cons (step1187 p h) (sat_cons (step765 p h) (sat_nil p)))
def c1191 : List Lit := [(1423, false), (1429, true)]
theorem step1191 (p : Nat → Bool) (h : Constraints p) : clause p c1191 = true :=
  Snake9.LocalRup.prove_clause [c1187, c766] c1191 (by decide) p (sat_cons (step1187 p h) (sat_cons (step766 p h) (sat_nil p)))
def c1192 : List Lit := [(1424, false), (1430, true)]
theorem step1192 (p : Nat → Bool) (h : Constraints p) : clause p c1192 = true :=
  Snake9.LocalRup.prove_clause [c1187, c767] c1192 (by decide) p (sat_cons (step1187 p h) (sat_cons (step767 p h) (sat_nil p)))
def c1193 : List Lit := [(1451, false), (1461, true)]
theorem step1193 (p : Nat → Bool) (h : Constraints p) : clause p c1193 = true :=
  Snake9.LocalRup.prove_clause [c1189, c810] c1193 (by decide) p (sat_cons (step1189 p h) (sat_cons (step810 p h) (sat_nil p)))
def c1194 : List Lit := [(1452, false), (1462, true)]
theorem step1194 (p : Nat → Bool) (h : Constraints p) : clause p c1194 = true :=
  Snake9.LocalRup.prove_clause [c1189, c811] c1194 (by decide) p (sat_cons (step1189 p h) (sat_cons (step811 p h) (sat_nil p)))
def c1195 : List Lit := [(1453, false), (1463, true)]
theorem step1195 (p : Nat → Bool) (h : Constraints p) : clause p c1195 = true :=
  Snake9.LocalRup.prove_clause [c1189, c812] c1195 (by decide) p (sat_cons (step1189 p h) (sat_cons (step812 p h) (sat_nil p)))
def c1196 : List Lit := [(1454, false), (1464, true)]
theorem step1196 (p : Nat → Bool) (h : Constraints p) : clause p c1196 = true :=
  Snake9.LocalRup.prove_clause [c1189, c813] c1196 (by decide) p (sat_cons (step1189 p h) (sat_cons (step813 p h) (sat_nil p)))
def c1197 : List Lit := [(1500, true)]
theorem step1197 (p : Nat → Bool) (h : Constraints p) : clause p c1197 = true :=
  Snake9.LocalRup.prove_clause [c1165, c861] c1197 (by decide) p (sat_cons (step1165 p h) (sat_cons (step861 p h) (sat_nil p)))
def c1198 : List Lit := [(1504, true)]
theorem step1198 (p : Nat → Bool) (h : Constraints p) : clause p c1198 = true :=
  Snake9.LocalRup.prove_clause [c1197, c863] c1198 (by decide) p (sat_cons (step1197 p h) (sat_cons (step863 p h) (sat_nil p)))
def c1199 : List Lit := [(1502, false), (1505, true)]
theorem step1199 (p : Nat → Bool) (h : Constraints p) : clause p c1199 = true :=
  Snake9.LocalRup.prove_clause [c1197, c864] c1199 (by decide) p (sat_cons (step1197 p h) (sat_cons (step864 p h) (sat_nil p)))
def c1200 : List Lit := [(1496, false), (1509, true)]
theorem step1200 (p : Nat → Bool) (h : Constraints p) : clause p c1200 = true :=
  Snake9.LocalRup.prove_clause [c1198, c866] c1200 (by decide) p (sat_cons (step1198 p h) (sat_cons (step866 p h) (sat_nil p)))
def c1201 : List Lit := [(1497, false), (1510, true)]
theorem step1201 (p : Nat → Bool) (h : Constraints p) : clause p c1201 = true :=
  Snake9.LocalRup.prove_clause [c1198, c868] c1201 (by decide) p (sat_cons (step1198 p h) (sat_cons (step868 p h) (sat_nil p)))
def c1202 : List Lit := [(1498, false), (1511, true)]
theorem step1202 (p : Nat → Bool) (h : Constraints p) : clause p c1202 = true :=
  Snake9.LocalRup.prove_clause [c1198, c870] c1202 (by decide) p (sat_cons (step1198 p h) (sat_cons (step870 p h) (sat_nil p)))
def c1203 : List Lit := [(1509, true)]
theorem step1203 (p : Nat → Bool) (h : Constraints p) : clause p c1203 = true :=
  Snake9.LocalRup.prove_clause [c532, c865, c1200, c1199, c856, c862, c854, c855, c184, c181] c1203 (by decide) p (sat_cons (step532 p h) (sat_cons (step865 p h) (sat_cons (step1200 p h) (sat_cons (step1199 p h) (sat_cons (step856 p h) (sat_cons (step862 p h) (sat_cons (step854 p h) (sat_cons (step855 p h) (sat_cons (step184 p h) (sat_cons (step181 p h) (sat_nil p)))))))))))
def c1204 : List Lit := [(1517, true)]
theorem step1204 (p : Nat → Bool) (h : Constraints p) : clause p c1204 = true :=
  Snake9.LocalRup.prove_clause [c1203, c871] c1204 (by decide) p (sat_cons (step1203 p h) (sat_cons (step871 p h) (sat_nil p)))
def c1205 : List Lit := [(1481, true)]
theorem step1205 (p : Nat → Bool) (h : Constraints p) : clause p c1205 = true :=
  Snake9.LocalRup.prove_clause [c525, c164, c836, c837, c835, c832, c157, c151] c1205 (by decide) p (sat_cons (step525 p h) (sat_cons (step164 p h) (sat_cons (step836 p h) (sat_cons (step837 p h) (sat_cons (step835 p h) (sat_cons (step832 p h) (sat_cons (step157 p h) (sat_cons (step151 p h) (sat_nil p)))))))))
def c1206 : List Lit := [(1485, true)]
theorem step1206 (p : Nat → Bool) (h : Constraints p) : clause p c1206 = true :=
  Snake9.LocalRup.prove_clause [c1205, c841] c1206 (by decide) p (sat_cons (step1205 p h) (sat_cons (step841 p h) (sat_nil p)))
def c1207 : List Lit := [(1518, true)]
theorem step1207 (p : Nat → Bool) (h : Constraints p) : clause p c1207 = true :=
  Snake9.LocalRup.prove_clause [c1206, c1203, c872] c1207 (by decide) p (sat_cons (step1206 p h) (sat_cons (step1203 p h) (sat_cons (step872 p h) (sat_nil p))))
def c1208 : List Lit := [(1445, true)]
theorem step1208 (p : Nat → Bool) (h : Constraints p) : clause p c1208 = true :=
  Snake9.LocalRup.prove_clause [c516, c791, c793, c788, c789, c785, c786, c110, c112, c116] c1208 (by decide) p (sat_cons (step516 p h) (sat_cons (step791 p h) (sat_cons (step793 p h) (sat_cons (step788 p h) (sat_cons (step789 p h) (sat_cons (step785 p h) (sat_cons (step786 p h) (sat_cons (step110 p h) (sat_cons (step112 p h) (sat_cons (step116 p h) (sat_nil p)))))))))))
def c1209 : List Lit := [(1587, true)]
theorem step1209 (p : Nat → Bool) (h : Constraints p) : clause p c1209 = true :=
  Snake9.LocalRup.prove_clause [c548, c948, c951, c941, c943, c930, c938, c936, c927, c249, c230] c1209 (by decide) p (sat_cons (step548 p h) (sat_cons (step948 p h) (sat_cons (step951 p h) (sat_cons (step941 p h) (sat_cons (step943 p h) (sat_cons (step930 p h) (sat_cons (step938 p h) (sat_cons (step936 p h) (sat_cons (step927 p h) (sat_cons (step249 p h) (sat_cons (step230 p h) (sat_nil p))))))))))))
def c1210 : List Lit := [(1595, true)]
theorem step1210 (p : Nat → Bool) (h : Constraints p) : clause p c1210 = true :=
  Snake9.LocalRup.prove_clause [c1209, c958] c1210 (by decide) p (sat_cons (step1209 p h) (sat_cons (step958 p h) (sat_nil p)))
def c1211 : List Lit := [(84, true), (1588, true)]
theorem step1211 (p : Nat → Bool) (h : Constraints p) : clause p c1211 = true :=
  Snake9.LocalRup.prove_clause [c548, c949, c946, c935, c937, c943, c944, c952, c938, c930, c249, c927, c230] c1211 (by decide) p (sat_cons (step548 p h) (sat_cons (step949 p h) (sat_cons (step946 p h) (sat_cons (step935 p h) (sat_cons (step937 p h) (sat_cons (step943 p h) (sat_cons (step944 p h) (sat_cons (step952 p h) (sat_cons (step938 p h) (sat_cons (step930 p h) (sat_cons (step249 p h) (sat_cons (step927 p h) (sat_cons (step230 p h) (sat_nil p))))))))))))))
def c1212 : List Lit := [(89, false), (80, false), (82, false)]
theorem step1212 (p : Nat → Bool) (h : Constraints p) : clause p c1212 = true :=
  Snake9.LocalRup.prove_clause [c548, c249, c230] c1212 (by decide) p (sat_cons (step548 p h) (sat_cons (step249 p h) (sat_cons (step230 p h) (sat_nil p))))
def c1213 : List Lit := [(101, false), (80, false), (1564, true)]
theorem step1213 (p : Nat → Bool) (h : Constraints p) : clause p c1213 = true :=
  Snake9.LocalRup.prove_clause [c536, c918, c911, c908, c913, c906, c921, c904, c903, c185, c198, c279, c188] c1213 (by decide) p (sat_cons (step536 p h) (sat_cons (step918 p h) (sat_cons (step911 p h) (sat_cons (step908 p h) (sat_cons (step913 p h) (sat_cons (step906 p h) (sat_cons (step921 p h) (sat_cons (step904 p h) (sat_cons (step903 p h) (sat_cons (step185 p h) (sat_cons (step198 p h) (sat_cons (step279 p h) (sat_cons (step188 p h) (sat_nil p))))))))))))))
def c1214 : List Lit := [(106, true), (1583, true)]
theorem step1214 (p : Nat → Bool) (h : Constraints p) : clause p c1214 = true :=
  Snake9.LocalRup.prove_clause [c547, c943, c936, c941, c939, c240, c241, c1140] c1214 (by decide) p (sat_cons (step547 p h) (sat_cons (step943 p h) (sat_cons (step936 p h) (sat_cons (step941 p h) (sat_cons (step939 p h) (sat_cons (step240 p h) (sat_cons (step241 p h) (sat_cons (step1140 p h) (sat_nil p)))))))))
def c1215 : List Lit := [(86, true), (1588, true)]
theorem step1215 (p : Nat → Bool) (h : Constraints p) : clause p c1215 = true :=
  Snake9.LocalRup.prove_clause [c548, c949, c942, c939, c940, c941, c944, c249, c952, c936, c230, c930, c927] c1215 (by decide) p (sat_cons (step548 p h) (sat_cons (step949 p h) (sat_cons (step942 p h) (sat_cons (step939 p h) (sat_cons (step940 p h) (sat_cons (step941 p h) (sat_cons (step944 p h) (sat_cons (step249 p h) (sat_cons (step952 p h) (sat_cons (step936 p h) (sat_cons (step230 p h) (sat_cons (step930 p h) (sat_cons (step927 p h) (sat_nil p))))))))))))))
def c1216 : List Lit := [(99, false), (1596, true)]
theorem step1216 (p : Nat → Bool) (h : Constraints p) : clause p c1216 = true :=
  Snake9.LocalRup.prove_clause [c1209, c539, c959, c1215, c962, c918, c913, c906, c911, c909, c191, c392, c206, c1214, c209, c952, c924, c932] c1216 (by decide) p (sat_cons (step1209 p h) (sat_cons (step539 p h) (sat_cons (step959 p h) (sat_cons (step1215 p h) (sat_cons (step962 p h) (sat_cons (step918 p h) (sat_cons (step913 p h) (sat_cons (step906 p h) (sat_cons (step911 p h) (sat_cons (step909 p h) (sat_cons (step191 p h) (sat_cons (step392 p h) (sat_cons (step206 p h) (sat_cons (step1214 p h) (sat_cons (step209 p h) (sat_cons (step952 p h) (sat_cons (step924 p h) (sat_cons (step932 p h) (sat_nil p)))))))))))))))))))
def c1217 : List Lit := [(1435, true), (1564, true)]
theorem step1217 (p : Nat → Bool) (h : Constraints p) : clause p c1217 = true :=
  Snake9.LocalRup.prove_clause [c514, c921, c904, c903, c918, c913, c905, c774, c775, c85, c88, c202] c1217 (by decide) p (sat_cons (step514 p h) (sat_cons (step921 p h) (sat_cons (step904 p h) (sat_cons (step903 p h) (sat_cons (step918 p h) (sat_cons (step913 p h) (sat_cons (step905 p h) (sat_cons (step774 p h) (sat_cons (step775 p h) (sat_cons (step85 p h) (sat_cons (step88 p h) (sat_cons (step202 p h) (sat_nil p)))))))))))))
def c1218 : List Lit := [(1435, false), (1461, true)]
theorem step1218 (p : Nat → Bool) (h : Constraints p) : clause p c1218 = true :=
  Snake9.LocalRup.prove_clause [c1208, c511, c1193, c802, c777, c780, c798, c771, c772, c814, c1190, c758, c760, c755, c753, c58, c28, c33] c1218 (by decide) p (sat_cons (step1208 p h) (sat_cons (step511 p h) (sat_cons (step1193 p h) (sat_cons (step802 p h) (sat_cons (step777 p h) (sat_cons (step780 p h) (sat_cons (step798 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step814 p h) (sat_cons (step1190 p h) (sat_cons (step758 p h) (sat_cons (step760 p h) (sat_cons (step755 p h) (sat_cons (step753 p h) (sat_cons (step58 p h) (sat_cons (step28 p h) (sat_cons (step33 p h) (sat_nil p)))))))))))))))))))
def c1219 : List Lit := [(1433, true), (1435, true)]
theorem step1219 (p : Nat → Bool) (h : Constraints p) : clause p c1219 = true :=
  Snake9.LocalRup.prove_clause [c515, c775, c774, c771, c772, c80, c90, c99] c1219 (by decide) p (sat_cons (step515 p h) (sat_cons (step775 p h) (sat_cons (step774 p h) (sat_cons (step771 p h) (sat_cons (step772 p h) (sat_cons (step80 p h) (sat_cons (step90 p h) (sat_cons (step99 p h) (sat_nil p)))))))))
end B112E104
