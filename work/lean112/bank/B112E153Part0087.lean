import B112E153Part0086
namespace B112E153
open Snake9.LocalRup
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def c7115 : List Lit := [(1091, true), (35, false), (1060, false)]
theorem step7115 (p : Nat → Bool) (h : Constraints p) : clause p c7115 = true :=
  Snake9.LocalRup.prove_clause [c6875, c6994, c6874, c6995, c7102, c7055, c4716, c1076, c1085, c1089, c4701, c1260, c7114, c2067, c1290, c7060, c1261, c3985, c1110, c1253, c1632, c1115, c4073, c6807, c6908, c7059, c1027, c1854, c6804] c7115 (by decide) p (sat_cons (step6875 p h) (sat_cons (step6994 p h) (sat_cons (step6874 p h) (sat_cons (step6995 p h) (sat_cons (step7102 p h) (sat_cons (step7055 p h) (sat_cons (step4716 p h) (sat_cons (step1076 p h) (sat_cons (step1085 p h) (sat_cons (step1089 p h) (sat_cons (step4701 p h) (sat_cons (step1260 p h) (sat_cons (step7114 p h) (sat_cons (step2067 p h) (sat_cons (step1290 p h) (sat_cons (step7060 p h) (sat_cons (step1261 p h) (sat_cons (step3985 p h) (sat_cons (step1110 p h) (sat_cons (step1253 p h) (sat_cons (step1632 p h) (sat_cons (step1115 p h) (sat_cons (step4073 p h) (sat_cons (step6807 p h) (sat_cons (step6908 p h) (sat_cons (step7059 p h) (sat_cons (step1027 p h) (sat_cons (step1854 p h) (sat_cons (step6804 p h) (sat_nil p))))))))))))))))))))))))))))))
def c7116 : List Lit := [(1123, true), (1052, true), (1091, false), (975, true), (35, false), (1012, false)]
theorem step7116 (p : Nat → Bool) (h : Constraints p) : clause p c7116 = true :=
  Snake9.LocalRup.prove_clause [c7102, c7055, c6875, c6994, c4716, c1076, c1085, c1089, c6766, c1173, c1140, c6015, c6819, c5995, c1058, c1027, c5172, c5638, c1201, c1207] c7116 (by decide) p (sat_cons (step7102 p h) (sat_cons (step7055 p h) (sat_cons (step6875 p h) (sat_cons (step6994 p h) (sat_cons (step4716 p h) (sat_cons (step1076 p h) (sat_cons (step1085 p h) (sat_cons (step1089 p h) (sat_cons (step6766 p h) (sat_cons (step1173 p h) (sat_cons (step1140 p h) (sat_cons (step6015 p h) (sat_cons (step6819 p h) (sat_cons (step5995 p h) (sat_cons (step1058 p h) (sat_cons (step1027 p h) (sat_cons (step5172 p h) (sat_cons (step5638 p h) (sat_cons (step1201 p h) (sat_cons (step1207 p h) (sat_nil p)))))))))))))))))))))
def c7117 : List Lit := [(974, true), (35, false), (1060, false)]
theorem step7117 (p : Nat → Bool) (h : Constraints p) : clause p c7117 = true :=
  Snake9.LocalRup.prove_clause [c6994, c6875, c4701, c1260, c4716, c3972, c7059] c7117 (by decide) p (sat_cons (step6994 p h) (sat_cons (step6875 p h) (sat_cons (step4701 p h) (sat_cons (step1260 p h) (sat_cons (step4716 p h) (sat_cons (step3972 p h) (sat_cons (step7059 p h) (sat_nil p))))))))
def c7118 : List Lit := [(35, false), (1060, false)]
theorem step7118 (p : Nat → Bool) (h : Constraints p) : clause p c7118 = true :=
  Snake9.LocalRup.prove_clause [c6875, c6994, c7102, c7055, c7114, c1114, c1138, c4701, c4716, c1260, c1076, c1085, c1089, c7062, c1855, c7115, c7117, c1854, c6766, c7116, c1173, c1237, c1140, c1326, c6819, c1370, c6094, c1172, c1178, c1027, c1143, c4057, c6906, c1117, c1108] c7118 (by decide) p (sat_cons (step6875 p h) (sat_cons (step6994 p h) (sat_cons (step7102 p h) (sat_cons (step7055 p h) (sat_cons (step7114 p h) (sat_cons (step1114 p h) (sat_cons (step1138 p h) (sat_cons (step4701 p h) (sat_cons (step4716 p h) (sat_cons (step1260 p h) (sat_cons (step1076 p h) (sat_cons (step1085 p h) (sat_cons (step1089 p h) (sat_cons (step7062 p h) (sat_cons (step1855 p h) (sat_cons (step7115 p h) (sat_cons (step7117 p h) (sat_cons (step1854 p h) (sat_cons (step6766 p h) (sat_cons (step7116 p h) (sat_cons (step1173 p h) (sat_cons (step1237 p h) (sat_cons (step1140 p h) (sat_cons (step1326 p h) (sat_cons (step6819 p h) (sat_cons (step1370 p h) (sat_cons (step6094 p h) (sat_cons (step1172 p h) (sat_cons (step1178 p h) (sat_cons (step1027 p h) (sat_cons (step1143 p h) (sat_cons (step4057 p h) (sat_cons (step6906 p h) (sat_cons (step1117 p h) (sat_cons (step1108 p h) (sat_nil p))))))))))))))))))))))))))))))))))))
def c7119 : List Lit := [(920, true), (1103, true), (1072, true), (1026, true), (1060, false)]
theorem step7119 (p : Nat → Bool) (h : Constraints p) : clause p c7119 = true :=
  Snake9.LocalRup.prove_clause [c6994, c6875, c7055, c4698, c1213, c4699, c7118, c938, c7114, c4045, c1665, c4285, c1619, c5785, c1332, c1217, c955, c2794, c1222, c3962, c1238, c1201, c1207] c7119 (by decide) p (sat_cons (step6994 p h) (sat_cons (step6875 p h) (sat_cons (step7055 p h) (sat_cons (step4698 p h) (sat_cons (step1213 p h) (sat_cons (step4699 p h) (sat_cons (step7118 p h) (sat_cons (step938 p h) (sat_cons (step7114 p h) (sat_cons (step4045 p h) (sat_cons (step1665 p h) (sat_cons (step4285 p h) (sat_cons (step1619 p h) (sat_cons (step5785 p h) (sat_cons (step1332 p h) (sat_cons (step1217 p h) (sat_cons (step955 p h) (sat_cons (step2794 p h) (sat_cons (step1222 p h) (sat_cons (step3962 p h) (sat_cons (step1238 p h) (sat_cons (step1201 p h) (sat_cons (step1207 p h) (sat_nil p))))))))))))))))))))))))
def c7120 : List Lit := [(955, false), (115, false), (954, false), (1002, false), (1012, false)]
theorem step7120 (p : Nat → Bool) (h : Constraints p) : clause p c7120 = true :=
  Snake9.LocalRup.prove_clause [c1138, c1171, c6762, c1856, c1980, c1059, c1855, c5890, c6781, c1139, c1172] c7120 (by decide) p (sat_cons (step1138 p h) (sat_cons (step1171 p h) (sat_cons (step6762 p h) (sat_cons (step1856 p h) (sat_cons (step1980 p h) (sat_cons (step1059 p h) (sat_cons (step1855 p h) (sat_cons (step5890 p h) (sat_cons (step6781 p h) (sat_cons (step1139 p h) (sat_cons (step1172 p h) (sat_nil p))))))))))))
def c7121 : List Lit := [(1103, false), (1002, false), (1060, false)]
theorem step7121 (p : Nat → Bool) (h : Constraints p) : clause p c7121 = true :=
  Snake9.LocalRup.prove_clause [c6998, c6994, c7118, c938, c1605, c7114, c1114, c6326, c1854, c6766, c1173, c1140, c6819, c1027, c1370, c6094] c7121 (by decide) p (sat_cons (step6998 p h) (sat_cons (step6994 p h) (sat_cons (step7118 p h) (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step7114 p h) (sat_cons (step1114 p h) (sat_cons (step6326 p h) (sat_cons (step1854 p h) (sat_cons (step6766 p h) (sat_cons (step1173 p h) (sat_cons (step1140 p h) (sat_cons (step6819 p h) (sat_cons (step1027 p h) (sat_cons (step1370 p h) (sat_cons (step6094 p h) (sat_nil p)))))))))))))))))
def c7122 : List Lit := [(1077, true), (1002, false), (1060, false)]
theorem step7122 (p : Nat → Bool) (h : Constraints p) : clause p c7122 = true :=
  Snake9.LocalRup.prove_clause [c6998, c6994, c6996, c6875, c6874, c7121, c7118, c938, c1605, c7114, c1114, c6326, c1854, c6766, c1173, c1140, c6819, c1027, c1258, c1260, c1253, c7119, c7120, c1033] c7122 (by decide) p (sat_cons (step6998 p h) (sat_cons (step6994 p h) (sat_cons (step6996 p h) (sat_cons (step6875 p h) (sat_cons (step6874 p h) (sat_cons (step7121 p h) (sat_cons (step7118 p h) (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step7114 p h) (sat_cons (step1114 p h) (sat_cons (step6326 p h) (sat_cons (step1854 p h) (sat_cons (step6766 p h) (sat_cons (step1173 p h) (sat_cons (step1140 p h) (sat_cons (step6819 p h) (sat_cons (step1027 p h) (sat_cons (step1258 p h) (sat_cons (step1260 p h) (sat_cons (step1253 p h) (sat_cons (step7119 p h) (sat_cons (step7120 p h) (sat_cons (step1033 p h) (sat_nil p)))))))))))))))))))))))))
def c7123 : List Lit := [(912, false), (1002, false), (1060, false)]
theorem step7123 (p : Nat → Bool) (h : Constraints p) : clause p c7123 = true :=
  Snake9.LocalRup.prove_clause [c6998, c6994, c7118, c938, c1605, c7114, c1114, c6326, c1854, c6766, c1173, c1140, c6819, c1027, c6814, c1038, c1138, c1171, c6762, c1856, c1923, c1619, c940, c1033, c1980, c1059, c1855, c6228, c6781, c1139, c1172] c7123 (by decide) p (sat_cons (step6998 p h) (sat_cons (step6994 p h) (sat_cons (step7118 p h) (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step7114 p h) (sat_cons (step1114 p h) (sat_cons (step6326 p h) (sat_cons (step1854 p h) (sat_cons (step6766 p h) (sat_cons (step1173 p h) (sat_cons (step1140 p h) (sat_cons (step6819 p h) (sat_cons (step1027 p h) (sat_cons (step6814 p h) (sat_cons (step1038 p h) (sat_cons (step1138 p h) (sat_cons (step1171 p h) (sat_cons (step6762 p h) (sat_cons (step1856 p h) (sat_cons (step1923 p h) (sat_cons (step1619 p h) (sat_cons (step940 p h) (sat_cons (step1033 p h) (sat_cons (step1980 p h) (sat_cons (step1059 p h) (sat_cons (step1855 p h) (sat_cons (step6228 p h) (sat_cons (step6781 p h) (sat_cons (step1139 p h) (sat_cons (step1172 p h) (sat_nil p))))))))))))))))))))))))))))))))
def c7124 : List Lit := [(1002, false), (1060, false)]
theorem step7124 (p : Nat → Bool) (h : Constraints p) : clause p c7124 = true :=
  Snake9.LocalRup.prove_clause [c6998, c6994, c7118, c6326, c1854, c6766, c938, c1605, c7114, c1114, c1173, c1140, c6819, c1027, c7121, c7122, c7123, c3985, c1290, c6842, c1326, c1855, c1237, c1058, c5995] c7124 (by decide) p (sat_cons (step6998 p h) (sat_cons (step6994 p h) (sat_cons (step7118 p h) (sat_cons (step6326 p h) (sat_cons (step1854 p h) (sat_cons (step6766 p h) (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step7114 p h) (sat_cons (step1114 p h) (sat_cons (step1173 p h) (sat_cons (step1140 p h) (sat_cons (step6819 p h) (sat_cons (step1027 p h) (sat_cons (step7121 p h) (sat_cons (step7122 p h) (sat_cons (step7123 p h) (sat_cons (step3985 p h) (sat_cons (step1290 p h) (sat_cons (step6842 p h) (sat_cons (step1326 p h) (sat_cons (step1855 p h) (sat_cons (step1237 p h) (sat_cons (step1058 p h) (sat_cons (step5995 p h) (sat_nil p))))))))))))))))))))))))))
def c7125 : List Lit := [(1103, true), (1060, false)]
theorem step7125 (p : Nat → Bool) (h : Constraints p) : clause p c7125 = true :=
  Snake9.LocalRup.prove_clause [c7103, c7102, c6875, c6995, c6994, c7105, c7124, c1089, c1085, c1076, c4700, c1260, c2066, c4707, c1215, c1083, c1077, c6799, c2057, c1199, c1206, c7118, c938, c1605, c6917, c1027, c7114, c1114, c3612, c1332, c1033, c1242, c1980, c4545, c1855, c1139, c6781, c1165, c7094, c1144, c5931, c1115, c7060, c1110] c7125 (by decide) p (sat_cons (step7103 p h) (sat_cons (step7102 p h) (sat_cons (step6875 p h) (sat_cons (step6995 p h) (sat_cons (step6994 p h) (sat_cons (step7105 p h) (sat_cons (step7124 p h) (sat_cons (step1089 p h) (sat_cons (step1085 p h) (sat_cons (step1076 p h) (sat_cons (step4700 p h) (sat_cons (step1260 p h) (sat_cons (step2066 p h) (sat_cons (step4707 p h) (sat_cons (step1215 p h) (sat_cons (step1083 p h) (sat_cons (step1077 p h) (sat_cons (step6799 p h) (sat_cons (step2057 p h) (sat_cons (step1199 p h) (sat_cons (step1206 p h) (sat_cons (step7118 p h) (sat_cons (step938 p h) (sat_cons (step1605 p h) (sat_cons (step6917 p h) (sat_cons (step1027 p h) (sat_cons (step7114 p h) (sat_cons (step1114 p h) (sat_cons (step3612 p h) (sat_cons (step1332 p h) (sat_cons (step1033 p h) (sat_cons (step1242 p h) (sat_cons (step1980 p h) (sat_cons (step4545 p h) (sat_cons (step1855 p h) (sat_cons (step1139 p h) (sat_cons (step6781 p h) (sat_cons (step1165 p h) (sat_cons (step7094 p h) (sat_cons (step1144 p h) (sat_cons (step5931 p h) (sat_cons (step1115 p h) (sat_cons (step7060 p h) (sat_cons (step1110 p h) (sat_nil p)))))))))))))))))))))))))))))))))))))))))))))
def c7126 : List Lit := [(1060, false)]
theorem step7126 (p : Nat → Bool) (h : Constraints p) : clause p c7126 = true :=
  Snake9.LocalRup.prove_clause [c6998, c7105, c7055, c7103, c7114, c7118, c938, c6326, c1605, c1854, c7124, c6917, c1027, c7125, c6072, c7091, c1117, c1033, c1028, c5378, c6983, c1108] c7126 (by decide) p (sat_cons (step6998 p h) (sat_cons (step7105 p h) (sat_cons (step7055 p h) (sat_cons (step7103 p h) (sat_cons (step7114 p h) (sat_cons (step7118 p h) (sat_cons (step938 p h) (sat_cons (step6326 p h) (sat_cons (step1605 p h) (sat_cons (step1854 p h) (sat_cons (step7124 p h) (sat_cons (step6917 p h) (sat_cons (step1027 p h) (sat_cons (step7125 p h) (sat_cons (step6072 p h) (sat_cons (step7091 p h) (sat_cons (step1117 p h) (sat_cons (step1033 p h) (sat_cons (step1028 p h) (sat_cons (step5378 p h) (sat_cons (step6983 p h) (sat_cons (step1108 p h) (sat_nil p)))))))))))))))))))))))
def c7127 : List Lit := [(105, true)]
theorem step7127 (p : Nat → Bool) (h : Constraints p) : clause p c7127 = true :=
  Snake9.LocalRup.prove_clause [c7126, c6994, c4693] c7127 (by decide) p (sat_cons (step7126 p h) (sat_cons (step6994 p h) (sat_cons (step4693 p h) (sat_nil p))))
def c7128 : List Lit := [(920, true)]
theorem step7128 (p : Nat → Bool) (h : Constraints p) : clause p c7128 = true :=
  Snake9.LocalRup.prove_clause [c7126, c6994, c4751] c7128 (by decide) p (sat_cons (step7126 p h) (sat_cons (step6994 p h) (sat_cons (step4751 p h) (sat_nil p))))
def c7129 : List Lit := [(71, false)]
theorem step7129 (p : Nat → Bool) (h : Constraints p) : clause p c7129 = true :=
  Snake9.LocalRup.prove_clause [c7126, c6994, c4702] c7129 (by decide) p (sat_cons (step7126 p h) (sat_cons (step6994 p h) (sat_cons (step4702 p h) (sat_nil p))))
def c7130 : List Lit := [(67, false)]
theorem step7130 (p : Nat → Bool) (h : Constraints p) : clause p c7130 = true :=
  Snake9.LocalRup.prove_clause [c7127, c6778] c7130 (by decide) p (sat_cons (step7127 p h) (sat_cons (step6778 p h) (sat_nil p)))
def c7131 : List Lit := [(1003, false)]
theorem step7131 (p : Nat → Bool) (h : Constraints p) : clause p c7131 = true :=
  Snake9.LocalRup.prove_clause [c7128, c7050] c7131 (by decide) p (sat_cons (step7128 p h) (sat_cons (step7050 p h) (sat_nil p)))
def c7132 : List Lit := [(994, true)]
theorem step7132 (p : Nat → Bool) (h : Constraints p) : clause p c7132 = true :=
  Snake9.LocalRup.prove_clause [c7129, c7102, c1076] c7132 (by decide) p (sat_cons (step7129 p h) (sat_cons (step7102 p h) (sat_cons (step1076 p h) (sat_nil p))))
def c7133 : List Lit := [(999, false)]
theorem step7133 (p : Nat → Bool) (h : Constraints p) : clause p c7133 = true :=
  Snake9.LocalRup.prove_clause [c7131, c1090] c7133 (by decide) p (sat_cons (step7131 p h) (sat_cons (step1090 p h) (sat_nil p)))
def c7134 : List Lit := [(103, false)]
theorem step7134 (p : Nat → Bool) (h : Constraints p) : clause p c7134 = true :=
  Snake9.LocalRup.prove_clause [c7132, c7131, c7127, c1866] c7134 (by decide) p (sat_cons (step7132 p h) (sat_cons (step7131 p h) (sat_cons (step7127 p h) (sat_cons (step1866 p h) (sat_nil p)))))
def c7135 : List Lit := [(995, false)]
theorem step7135 (p : Nat → Bool) (h : Constraints p) : clause p c7135 = true :=
  Snake9.LocalRup.prove_clause [c7132, c7133, c1086] c7135 (by decide) p (sat_cons (step7132 p h) (sat_cons (step7133 p h) (sat_cons (step1086 p h) (sat_nil p))))
def c7136 : List Lit := [(1055, true)]
theorem step7136 (p : Nat → Bool) (h : Constraints p) : clause p c7136 = true :=
  Snake9.LocalRup.prove_clause [c7134, c1213] c7136 (by decide) p (sat_cons (step7134 p h) (sat_cons (step1213 p h) (sat_nil p)))
def c7137 : List Lit := [(75, true)]
theorem step7137 (p : Nat → Bool) (h : Constraints p) : clause p c7137 = true :=
  Snake9.LocalRup.prove_clause [c7135, c1077] c7137 (by decide) p (sat_cons (step7135 p h) (sat_cons (step1077 p h) (sat_nil p)))
def c7138 : List Lit := [(1057, false)]
theorem step7138 (p : Nat → Bool) (h : Constraints p) : clause p c7138 = true :=
  Snake9.LocalRup.prove_clause [c7136, c7126, c1221] c7138 (by decide) p (sat_cons (step7136 p h) (sat_cons (step7126 p h) (sat_cons (step1221 p h) (sat_nil p))))
def c7139 : List Lit := [(66, false)]
theorem step7139 (p : Nat → Bool) (h : Constraints p) : clause p c7139 = true :=
  Snake9.LocalRup.prove_clause [c7137, c6773] c7139 (by decide) p (sat_cons (step7137 p h) (sat_cons (step6773 p h) (sat_nil p)))
def c7140 : List Lit := [(108, true)]
theorem step7140 (p : Nat → Bool) (h : Constraints p) : clause p c7140 = true :=
  Snake9.LocalRup.prove_clause [c7138, c1215] c7140 (by decide) p (sat_cons (step7138 p h) (sat_cons (step1215 p h) (sat_nil p)))
def c7141 : List Lit := []
theorem step7141 (p : Nat → Bool) (h : Constraints p) : clause p c7141 = true :=
  Snake9.LocalRup.prove_clause [c7140, c7139, c7130, c6782] c7141 (by decide) p (sat_cons (step7140 p h) (sat_cons (step7139 p h) (sat_cons (step7130 p h) (sat_cons (step6782 p h) (sat_nil p)))))
end B112E153
